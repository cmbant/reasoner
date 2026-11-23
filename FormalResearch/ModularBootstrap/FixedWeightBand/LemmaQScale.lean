module

public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP

/-!
# Scale-flexible Lemma Q at every fixed `(w, Q)` (`wone:Q`, `lower_o1_two_edge.tex`)

## What the Virasoro proof needs, and what this file supplies

The paper (`vlo:order`, stages (ii)-(iii)) chooses the dimensionless bootstrap scale `b_V = √(c₀/2)`
**last among the scales**, as a minimum of caps (chart cap of Proposition P, annulus, window, ...),
and only afterwards fixes the constants that depend on it, in particular the lobe exponent `κ` of
`wone:Q (1)`.  Two statements are therefore needed at *every* scale `0 < b ≤ chartBV r₁` (the chart
cap of Proposition P):

* the type-(II) envelope and holomorphy of `wone:Q (2)` on the disc `|u| ≤ A_{c'}(b)²`, with
  constants **independent of `b`** (they must not feed back into the choice of `b`);
* the lobe/mass statements `wone:Q (1)` and `(3)` on the same disc, with `δ_lobe` replaced by the
  scale-dependent `δ_lobe(b) = M[g]⁻¹ ∫_0^{Δ(A_{c'}(b)²)} |g| V dt` and constants (`C_gap`, `κ_gap`,
  and the threshold on `c'`) allowed to depend on `b` (stage (iii) and (iv)).

The Virasoro proof (`ConcreteBootstrap/LemmaQ.lean`, `BootstrapHB.lean`) uses exactly
`virasoroACAt`, `virasoroDeltaLobeAt`, `virasoroDeltaLobe_le_virasoroDeltaLobeAt`, `lemmaQ_part1At`,
`lemmaQ_part3At`, the full-scale `lemmaQ_part2` restricted to the smaller disc, and the lemma
`virasoro_lobe_scale_down` (scale-`b` lobe facts imply the full-scale ones).  The scale `b` is
`virasoroBVChoice = min virasoroBV √(virasoroScaleThresh/4)` (`Contour/VirasoroScaleChoice.lean`).

`FixedWeightTip/PropositionP.lean` proves Proposition P and `lemmaQ_general_part1`-`3` only at the
single scale `chartBV D.r₁`.  They are not enough, because the final scale is a minimum with the
strip/contour cap, which is smaller.  Everything else Lemma Q needs is weight-free (Langer chart) or
already general in `(w, Q)` (`UniformPropositionPData`, `psiTilde`, `psiTilde_typeII_envelope_general`).

## Method

For `0 < b ≤ chartBV r₁` put `r' := 2 C_b b²`.  Then `0 < r' ≤ r₁` and `chartBV r' = b`, so
`chartAC r' c' = √2 b c'^{1/3} = chartACAt b c'`.  Shrinking the disc radius of the uniform
Proposition P data from `r₁` to `r'` is a restriction of the two `r₁`-dependent fields
(`shrinkUniformData`), and `lemmaQ_general_part1` / `lemmaQ_general_part3` for the shrunk data are
the scale-`b` statements.  The envelope (`part2`) is obtained from the unshrunk data by monotonicity
of the disc, which is what makes its constants independent of `b`.

## Declarations (consumed by WP10 and WP11 of the fixed-weight plan)

* `chartACAt`, `chartACAt_sq`, `chartACAt_pos`, `chartACAt_sq_le_chartAC_sq`,
  `chartACAt_sq_le_virasoroAC_sq`, `closedBall_chartACAt_subset_psiDom`: the scale-`b` disc
  (`virasoroACAt`-family).
* `deltaLobeAt`, `deltaLobe_eq_deltaLobeAt`, `deltaLobeAt_anti`, `deltaLobe_le_deltaLobeAt`:
  `δ_lobe(b)` is antitone in `b`; in particular `δ_lobe ≤ δ_lobe(b)`.
* `lemmaQ_general_part1At`: `wone:Q (1)` at scale `b` (`δ_lobe(b) ≤ C e^{-κ c'} < 1/2`,
  `Δ(A_{c'}(b)²) < T`); constants depend on `b`.
* `lemmaQ_general_part2At`: `wone:Q (2)` on the scale-`b` disc, constants independent of `b`.
* `lemmaQ_general_part3At`: `wone:Q (3)` at scale `b`; the threshold depends on `b`.
* `lemmaQ_general_lobe_scale_down`: the scale-`b` lobe facts give the full-scale ones.
* `lemmaQ_scale_of_problem`: unconditional for every `prob : FixedWeightProblem`; the uniform data
  exist (`UniformPropositionPData.of_problem`) and the scale range `0 < b ≤ chartBV D.r₁` contains
  `chartBV D.r₁`, so the statements are non-vacuous.  `chartBV D.r₁ ≤ virasoroBV`
  (`chartBV_le_virasoroBV`), which is the cap `YVInputFor b` and the Langer chart lemmas expect.

The `w = 1` identifications with the Virasoro declarations are in `LemmaQScaleBridge.lean`.  Nothing
in this file is conditional on a named hypothesis.  Not covered: the threshold in `part3At` depends on
`b` (it is chosen after `b`, `vlo:order` stage (iv)); a `b`-uniform threshold would need the
`part3` proof repeated on the unshrunk data.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing PoissonJensen WeightAxioms TipFront ConcreteBootstrap FixedWeightTip
  FormalResearch.Special

/-! ### Shrinking the Proposition P disc radius -/

/-- Restriction of the `r₁`-dependent fields of `PropositionPAxioms` to a smaller radius. -/
noncomputable def shrinkPAxioms {prob : FixedWeightProblem} {c' : ℝ}
    (P : PropositionPAxioms prob c') {r : ℝ} (hr : 0 < r) (hrle : r ≤ P.r_1) :
    PropositionPAxioms prob c' :=
  { P with
    r_1 := r
    hr1_pos := hr
    hr1_le := hrle.trans P.hr1_le
    p2_Q_ne_zero := fun hb => P.p2_Q_ne_zero (closedBall_subset_closedBall hrle hb)
    p2_disc_asymp := fun hb => P.p2_disc_asymp (closedBall_subset_closedBall hrle hb) }

/-- Uniform Proposition P data with the disc radius `r₁` replaced by a smaller `r`. -/
noncomputable def shrinkUniformData {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {r : ℝ} (hr : 0 < r) (hrle : r ≤ D.r_1) : UniformPropositionPData prob :=
  { D with
    r_1 := r
    hr1_pos := hr
    hr1_le := hrle.trans D.hr1_le
    pAt := fun {_} hc' => shrinkPAxioms (D.pAt hc') hr (by rw [D.uniform_r_1 hc']; exact hrle)
    uniform_r_1 := fun _ => rfl
    uniform_C_e := fun hc' => D.uniform_C_e hc'
    uniform_p_e := fun hc' => D.uniform_p_e hc'
    uniform_c_band := fun hc' => D.uniform_c_band hc'
    uniform_C_up := fun hc' => D.uniform_C_up hc'
    uniform_p_u := fun hc' => D.uniform_p_u hc'
    uniform_Q_star := fun hc' => D.uniform_Q_star hc'
    uniform_ηV_le := fun hc' => D.uniform_ηV_le hc'
    disc_err_tendsto_zero := D.disc_err_tendsto_zero
    vac_err_zero := fun hc' => D.vac_err_zero hc' }

lemma shrinkUniformData_r_1 {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {r : ℝ} (hr : 0 < r) (hrle : r ≤ D.r_1) : (shrinkUniformData D hr hrle).r_1 = r := rfl

lemma shrinkUniformData_c₀ {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {r : ℝ} (hr : 0 < r) (hrle : r ≤ D.r_1) : (shrinkUniformData D hr hrle).c₀ = D.c₀ := rfl

/-! ### The scale-`b` chart disc -/

/-- Chart radius `A_{c'}(b) = √2 b c'^{1/3}` at scale `b`; `chartACAt (chartBV r₁) = chartAC r₁`. -/
noncomputable def chartACAt (b c' : ℝ) : ℝ := √2 * b * c' ^ (1 / 3 : ℝ)

lemma chartACAt_chartBV (r_1 c' : ℝ) : chartACAt (chartBV r_1) c' = chartAC r_1 c' := rfl

lemma chartACAt_sq (b c' : ℝ) (hc' : 0 ≤ c') :
    chartACAt b c' ^ 2 = 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := by
  unfold chartACAt
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2,
    ← Real.rpow_mul hc']
  norm_num

lemma chartACAt_pos {b c' : ℝ} (hb : 0 < b) (hc' : 0 < c') : 0 < chartACAt b c' := by
  unfold chartACAt; positivity

lemma chartACAt_sq_le_chartAC_sq {b r_1 c' : ℝ} (hb : 0 ≤ b) (hle : b ≤ chartBV r_1)
    (hc' : 0 ≤ c') : chartACAt b c' ^ 2 ≤ chartAC r_1 c' ^ 2 := by
  rw [chartACAt_sq b c' hc', chartAC_sq r_1 c' hc']
  have hsq : b ^ 2 ≤ chartBV r_1 ^ 2 := pow_le_pow_left₀ hb hle 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq zero_le_two)
    (Real.rpow_nonneg hc' _)

lemma chartACAt_sq_le_virasoroAC_sq {b r_1 c' : ℝ} (hr1 : 0 < r_1) (hb : 0 ≤ b)
    (hle : b ≤ chartBV r_1) (hc' : 0 ≤ c') :
    chartACAt b c' ^ 2 ≤ virasoroAC c' ^ 2 :=
  (chartACAt_sq_le_chartAC_sq hb hle hc').trans (chartAC_sq_le_virasoroAC_sq hr1 hc')

lemma closedBall_chartACAt_subset_psiDom {b r_1 c' : ℝ} (hr1 : 0 < r_1) (hb : 0 ≤ b)
    (hle : b ≤ chartBV r_1) (hc' : 0 < c') :
    closedBall (0 : ℂ) (chartACAt b c' ^ 2) ⊆ psiDom c' :=
  (closedBall_subset_closedBall (chartACAt_sq_le_chartAC_sq hb hle hc'.le)).trans
    (closedBall_chartAC_subset_psiDom hr1 hc')

/-! ### The radius `r' = 2 C_b b²` realising the scale `b` -/

/-- Disc radius whose chart scale is exactly `b`. -/
noncomputable def scaleR1 (b : ℝ) : ℝ := 2 * chartParams.C_b * b ^ 2

lemma scaleR1_pos {b : ℝ} (hb : 0 < b) : 0 < scaleR1 b := by
  unfold scaleR1
  have := chartParams.hCb_pos
  positivity

lemma chartBV_scaleR1 {b : ℝ} (hb : 0 < b) (hb_le : b ≤ virasoroBV) :
    chartBV (scaleR1 b) = b := by
  have hCb := chartParams.hCb_pos
  unfold chartBV scaleR1
  rw [show 2 * chartParams.C_b * b ^ 2 / (2 * chartParams.C_b) = b ^ 2 by field_simp,
    Real.sqrt_sq hb.le]
  exact min_eq_right hb_le

lemma scaleR1_le {b r_1 : ℝ} (hr1 : 0 < r_1) (hb : 0 < b) (hle : b ≤ chartBV r_1) :
    scaleR1 b ≤ r_1 := by
  have hCb := chartParams.hCb_pos
  have h1 := two_chartBV_sq_le hr1
  rw [le_div_iff₀ hCb] at h1
  have hsq : b ^ 2 ≤ chartBV r_1 ^ 2 := pow_le_pow_left₀ hb.le hle 2
  unfold scaleR1
  nlinarith

lemma chartAC_scaleR1 {b : ℝ} (hb : 0 < b) (hb_le : b ≤ virasoroBV) (c' : ℝ) :
    chartAC (scaleR1 b) c' = chartACAt b c' := by
  rw [← chartACAt_chartBV, chartBV_scaleR1 hb hb_le]

/-! ### The scale-`b` far lobe -/

/-- Far-lobe normalised mass at scale `b`: `M[g]⁻¹ ∫_0^{Δ(A_{c'}(b)²)} |g| V dt`. -/
noncomputable def deltaLobeAt (prob : FixedWeightProblem) (b c' : ℝ) (g : ℝ → ℝ) : ℝ :=
  (prob.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartACAt b c' ^ 2)),
      |g t| * prob.cardyV (c' / 12) t

lemma deltaLobe_eq_deltaLobeAt (prob : FixedWeightProblem) (r_1 c' : ℝ) (g : ℝ → ℝ) :
    deltaLobe prob r_1 c' g = deltaLobeAt prob (chartBV r_1) c' g := rfl

lemma deltaLobe_scaleR1 (prob : FixedWeightProblem) {b : ℝ} (hb : 0 < b) (hb_le : b ≤ virasoroBV)
    (c' : ℝ) (g : ℝ → ℝ) :
    deltaLobe prob (scaleR1 b) c' g = deltaLobeAt prob b c' g := by
  unfold deltaLobe deltaLobeAt
  rw [chartAC_scaleR1 hb hb_le]

/-- `δ_lobe(b)` is antitone in the scale: a smaller scale moves the lobe endpoint `Δ(A_{c'}(b)²)`
up and enlarges the lobe. -/
lemma deltaLobeAt_anti {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {b b' c' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') (hb'_le : b' ≤ chartBV D.r_1)
    (hc' : D.c₀ ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g) :
    deltaLobeAt prob b' c' g ≤ deltaLobeAt prob b c' g := by
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'
  have hb'_pos : 0 < b' := hb.trans_le hbb'
  have hA'_le : chartACAt b' c' ^ 2 ≤ virasoroAC c' ^ 2 :=
    chartACAt_sq_le_virasoroAC_sq D.hr1_pos hb'_pos.le hb'_le hc'_pos.le
  have hA_le : chartACAt b c' ^ 2 ≤ chartACAt b' c' ^ 2 := by
    rw [chartACAt_sq b c' hc'_pos.le, chartACAt_sq b' c' hc'_pos.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hbb' 2) zero_le_two)
      (Real.rpow_nonneg hc'_pos.le _)
  have hΔ_lo : 0 ≤ virasoroDeltaChart c' (chartACAt b' c' ^ 2) :=
    (virasoroDeltaChart_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]; exact hA'_le)).le
  have hΔ_le : virasoroDeltaChart c' (chartACAt b' c' ^ 2) ≤
      virasoroDeltaChart c' (chartACAt b c' ^ 2) :=
    (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [sq_nonneg (chartACAt b c')], hA_le.trans hA'_le⟩
      ⟨by linarith [sq_nonneg (chartACAt b' c')], hA'_le⟩ hA_le
  unfold deltaLobeAt
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hM_pos.le)
  rw [intervalIntegral.integral_of_le hΔ_lo, intervalIntegral.integral_of_le (hΔ_lo.trans hΔ_le)]
  refine setIntegral_mono_set (hg.int_cardy.mono_set Ioc_subset_Ioi_self) ?_
    (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hΔ_le⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (abs_nonneg _) (D.cardyV_nonneg hc' ht.1.le)

/-- The full-scale lobe is bounded by the lobe at any smaller scale `0 < b ≤ chartBV D.r₁`. -/
lemma deltaLobe_le_deltaLobeAt {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {b c' : ℝ} (hb : 0 < b) (hb_le : b ≤ chartBV D.r_1) (hc' : D.c₀ ≤ c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g) :
    deltaLobe prob D.r_1 c' g ≤ deltaLobeAt prob b c' g :=
  deltaLobeAt_anti D hb hb_le le_rfl hc' hg hM_pos

/-! ### Lemma Q at scale `b` -/

/-- **Lemma Q (`wone:Q`), part (1), at scale `0 < b ≤ chartBV D.r₁`**: `δ_lobe(b) ≤ C e^{-κ c'} < 1/2`
and `Δ(A_{c'}(b)²) < T` for every weakly feasible test.  The constants depend on `b`
(`vlo:order`, stage (iii)). -/
theorem lemmaQ_general_part1At {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {b : ℝ} (hb : 0 < b) (hb_le : b ≤ chartBV D.r_1) :
    ∃ c_gap C_gap κ_gap : ℝ, D.c₀ ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_gap ≤ c' →
        prob.IsWeaklyFeasible (c' / 12) T g →
          0 < prob.cardyNorm (c' / 12) g ∧
          deltaLobeAt prob b c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
          deltaLobeAt prob b c' g < 1 / 2 ∧
          virasoroDeltaChart c' (chartACAt b c' ^ 2) < T := by
  have hbV : b ≤ virasoroBV := hb_le.trans (chartBV_le_virasoroBV _)
  obtain ⟨c_gap, C_gap, κ_gap, hc, hC, hκ, h⟩ :=
    lemmaQ_general_part1 (shrinkUniformData D (scaleR1_pos hb) (scaleR1_le D.hr1_pos hb hb_le))
  refine ⟨c_gap, C_gap, κ_gap, hc, hC, hκ, fun {c' T g} hc' hwf => ?_⟩
  have h1 : 0 < prob.cardyNorm (c' / 12) g ∧
      deltaLobe prob (scaleR1 b) c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
      deltaLobe prob (scaleR1 b) c' g < 1 / 2 ∧
      virasoroDeltaChart c' (chartAC (scaleR1 b) c' ^ 2) < T := h hc' hwf
  rwa [deltaLobe_scaleR1 prob hb hbV, chartAC_scaleR1 hb hbV] at h1

/-- **Lemma Q (`wone:Q`), part (2), on the scale-`b` disc**: holomorphy of `psiTilde` on
`psiDom c' ⊇ closedBall 0 (A_{c'}(b)²)`, real-axis values and sign (`H2+`), and the type-(II)
envelope.  The constants `c₂`, `C₀` do **not** depend on `b`. -/
theorem lemmaQ_general_part2At {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c₂ C₀ : ℝ, D.c₀ ≤ c₂ ∧ 0 < C₀ ∧
      ∀ {b : ℝ}, 0 < b → b ≤ chartBV D.r_1 →
        ∀ {c' : ℝ}, c₂ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
            AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') ∧
            (∀ u : ℝ, |u| ≤ chartACAt b c' ^ 2 →
              (psiTilde prob c' g (u : ℂ)).im = 0 ∧
              (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re)) ∧
            ∀ u : ℂ, u ∈ closedBall (0 : ℂ) (chartACAt b c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
              ‖psiTilde prob c' g u‖ ≤
                C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                  ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  obtain ⟨c₂, C₀, hc₂, hC₀, h⟩ := lemmaQ_general_part2 D
  refine ⟨c₂, C₀, hc₂, hC₀, fun {b} hb hb_le {c'} hc' {g} hg hM => ?_⟩
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le (hc₂.trans hc')
  have hsq := chartACAt_sq_le_chartAC_sq hb.le hb_le hc'_pos.le
  obtain ⟨han, hreal, henv⟩ := h hc' hg hM
  refine ⟨han, fun u hu => hreal u (hu.trans hsq), fun u hu hcut => ?_⟩
  exact henv u (closedBall_subset_closedBall hsq hu) hcut

/-- **Lemma Q (`wone:Q`), part (3), at scale `0 < b ≤ chartBV D.r₁`**: real-axis sign, total `L¹` mass
`≤ 1`, half-mass negative tail and the top-tail transport identities on
`[-A_{c'}(b)², A_{c'}(b)²]`.  The threshold on `c'` depends on `b` (`vlo:order`, stage (iv)). -/
theorem lemmaQ_general_part3At {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {b : ℝ} (hb : 0 < b) (hb_le : b ≤ chartBV D.r_1) :
    ∃ c₃ : ℝ, D.c₀ ≤ c₃ ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c₃ ≤ c' →
        prob.IsWeaklyFeasible (c' / 12) T g →
          let A2 := chartACAt b c' ^ 2
          let M := prob.cardyNorm (c' / 12) g
          (∀ u : ℝ, |u| ≤ A2 → T ≤ virasoroDeltaChart c' u →
            0 ≤ (psiTilde prob c' g (u : ℂ)).re) ∧
          (∫ u in (-A2)..A2, ‖psiTilde prob c' g (u : ℂ)‖ ≤ 1) ∧
          (T < virasoroDeltaChart c' (-A2) →
            virasoroDeltaChart c' A2 < T →
            chartUT c' T ∈ Ioo (-A2) A2) ∧
          (T < virasoroDeltaChart c' (-A2) →
            virasoroDeltaChart c' A2 ≤ T →
            chartUT c' T ∈ Icc (-A2) A2 ∧
            (∀ u ∈ Icc (-A2) (chartUT c' T), 0 ≤ (psiTilde prob c' g (u : ℂ)).re) ∧
            ((1 / 2 : ℝ) - deltaLobeAt prob b c' g ≤
              ∫ u in (chartUT c' T)..A2, max 0 (-(psiTilde prob c' g (u : ℂ)).re))) ∧
          (∀ R' : ℝ, 0 ≤ R' → R' ≤ A2 → T ≤ virasoroDeltaChart c' (-R') →
            ∫ u in (-R')..A2, (psiTilde prob c' g (u : ℂ)).re =
              M⁻¹ * ∫ t in (virasoroDeltaChart c' A2)..(virasoroDeltaChart c' (-R')),
                g t * prob.cardyV (c' / 12) t ∧
            ∫ u in (-R')..A2, (psiTilde prob c' g (u : ℂ)).re ≤ deltaLobeAt prob b c' g) := by
  have hbV : b ≤ virasoroBV := hb_le.trans (chartBV_le_virasoroBV _)
  obtain ⟨c₃, hc₃, h⟩ :=
    lemmaQ_general_part3 (shrinkUniformData D (scaleR1_pos hb) (scaleR1_le D.hr1_pos hb hb_le))
  refine ⟨c₃, hc₃, fun {c' T g} hc' hwf => ?_⟩
  have h1 := h hc' hwf
  dsimp only at h1 ⊢
  rw [shrinkUniformData_r_1] at h1
  rwa [deltaLobe_scaleR1 prob hb hbV, chartAC_scaleR1 hb hbV] at h1

/-- The scale-`b` lobe facts give the full-scale ones (`δ_lobe ≤ δ_lobe(b)`, and
`Δ(A_{c'}(r₁)²) ≤ Δ(A_{c'}(b)²) < T`), so `wone:Q (1)` at scale `b` implies it at scale `chartBV D.r₁`
with the constants of scale `b`. -/
lemma lemmaQ_general_lobe_scale_down {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {b C_gap κ_gap c' T : ℝ} (hb : 0 < b) (hb_le : b ≤ chartBV D.r_1) (hc' : D.c₀ ≤ c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (hdl_bd : deltaLobeAt prob b c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : deltaLobeAt prob b c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (chartACAt b c' ^ 2) < T) :
    chartACAt b c' ^ 2 ≤ chartAC D.r_1 c' ^ 2 ∧
    deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
    deltaLobe prob D.r_1 c' g < 1 / 2 ∧
    virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T := by
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'
  have hA_le := chartACAt_sq_le_chartAC_sq hb.le hb_le hc'_pos.le
  have hA_vir := chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
  have hle : deltaLobe prob D.r_1 c' g ≤ deltaLobeAt prob b c' g :=
    deltaLobe_le_deltaLobeAt D hb hb_le hc' hg hM_pos
  have hΔ_le : virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) ≤
      virasoroDeltaChart c' (chartACAt b c' ^ 2) :=
    (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [sq_nonneg (chartACAt b c')], hA_le.trans hA_vir⟩
      ⟨by linarith [sq_nonneg (chartAC D.r_1 c')], hA_vir⟩ hA_le
  exact ⟨hA_le, hle.trans hdl_bd, hle.trans_lt hdl_half, hΔ_le.trans_lt hT_A2⟩

/-- **Scale-flexible Lemma Q (`wone:Q`), unconditional at every fixed `(w, Q)`.**  There are uniform
Proposition P data `D` such that the envelope of part (2) holds with `b`-free constants on every
scale disc `0 < b ≤ chartBV D.r₁`, and parts (1), (3) hold at every such scale. -/
theorem lemmaQ_scale_of_problem (prob : FixedWeightProblem) :
    ∃ D : UniformPropositionPData prob,
      (∃ c₂ C₀ : ℝ, D.c₀ ≤ c₂ ∧ 0 < C₀ ∧
        ∀ {b : ℝ}, 0 < b → b ≤ chartBV D.r_1 →
          ∀ {c' : ℝ}, c₂ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
            0 < prob.cardyNorm (c' / 12) g →
              AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') ∧
              (∀ u : ℝ, |u| ≤ chartACAt b c' ^ 2 →
                (psiTilde prob c' g (u : ℂ)).im = 0 ∧
                (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re)) ∧
              ∀ u : ℂ, u ∈ closedBall (0 : ℂ) (chartACAt b c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
                ‖psiTilde prob c' g u‖ ≤
                  C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                    ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) ∧
      ∀ {b : ℝ}, 0 < b → b ≤ chartBV D.r_1 →
        (∃ c_gap C_gap κ_gap : ℝ, D.c₀ ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
          ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_gap ≤ c' →
            prob.IsWeaklyFeasible (c' / 12) T g →
              0 < prob.cardyNorm (c' / 12) g ∧
              deltaLobeAt prob b c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
              deltaLobeAt prob b c' g < 1 / 2 ∧
              virasoroDeltaChart c' (chartACAt b c' ^ 2) < T) ∧
        (∃ c₃ : ℝ, D.c₀ ≤ c₃ ∧
          ∀ {c' T : ℝ} {g : ℝ → ℝ}, c₃ ≤ c' →
            prob.IsWeaklyFeasible (c' / 12) T g →
              ∫ u in (-(chartACAt b c' ^ 2))..(chartACAt b c' ^ 2),
                ‖psiTilde prob c' g (u : ℂ)‖ ≤ 1) := by
  obtain ⟨D⟩ := UniformPropositionPData.of_problem prob
  refine ⟨D, lemmaQ_general_part2At D, fun {b} hb hb_le => ⟨lemmaQ_general_part1At D hb hb_le, ?_⟩⟩
  obtain ⟨c₃, hc₃, h⟩ := lemmaQ_general_part3At D hb hb_le
  exact ⟨c₃, hc₃, fun {c' T g} hc' hwf => (h hc' hwf).2.1⟩

/-! ### Axiom Checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.deltaLobeAt_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deltaLobeAt_anti

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemmaQ_general_part1At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_general_part1At

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemmaQ_general_part2At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_general_part2At

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemmaQ_general_part3At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_general_part3At

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemmaQ_general_lobe_scale_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_general_lobe_scale_down

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemmaQ_scale_of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_scale_of_problem

end FormalResearch.ModularBootstrap.FixedWeightBand
