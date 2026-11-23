module

public import FormalResearch.ModularBootstrap.FixedWeight.StrongDuality
public import FormalResearch.ModularBootstrap.Duality.OptimalMeasure
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.TheoremJ
public import FormalResearch.ModularBootstrap.Contour.VirasoroScaleChoice

/-!
# Fixed-Weight Corollary E1 (`dual_spectrum.tex`, `ds:E1`)

Generalises `Duality.OptimalMeasure` to every fixed-weight problem `prob : FixedWeightProblem`:

* `corollary_E1_exact_gap` (unconditional for any `c̃ > 0`, `c̃ ≥ 12 S`, `T_V(c̃) > 0`):
  existence of a crossing measure `ν_*` with gap `min supp ν_* = T_V(c̃)`, attaining `Δ_best(c̃)`.
* Explicit named hypotheses (`Prop`) for the `T_V(c̃) = T_*(c̃) + O_{w,Q}(1)` inputs of
  Corollary E1 (`dual_spectrum.tex`, `ds:E1`):
  - `FixedWeightLowerBoundInput prob` (Theorem W1'(1), `wone:genlower(1)`; proved for every `prob`
    by `FixedWeightBand.fixedWeightLowerBoundInput_of_problem`, and for `virasoroProblem` also by
    `virasoro_lowerBoundInput` via `Contour.theoremJ_T_V`);
  - `TheoremC15UpperInput prob` (the `O(1)` upper half of Theorem C15 / Theorem ctu.5,
    `thm:fixed-weight-expansion`; proved for `virasoroProblem` by
    `Upper.Ramped.theoremC15UpperInput_virasoro` through the ramped comb of Lemma U*,
    `CFT/notes/n2_ramped_comb.tex` `rem:thmU`, and for every `prob` with `prob.w = 1`, in particular
    `N = 1` super-Virasoro, by `Upper.Ramped.theoremC15UpperInput_prob`; open for `w > 1`);
  - `WeakThresholdLowerBoundAt` (satisfied unconditionally at `virasoroProblem` by
    `Integration.theoremA_T_V`), with non-vacuity theorems `thresholdLowerBoundAt_nonvacuous`,
    `thresholdUpperBoundAt_nonvacuous`, and `weakThresholdLowerBound_virasoro`.
* `corollary_E1`: Corollary E1 (exact gap `T_V(c̃) = T_*(c̃) + O_{w,Q}(1)`, attainment of `Δ_best`,
  and the `(Gap)` condition `liminf_j (τ_j - T_*(c̃_j)) / c̃_j^{1/3} ≥ 0` of `sr:Sigma0`,
  `sr:Sigma`) proved given `FixedWeightLowerBoundInput prob` and `TheoremC15UpperInput prob`.
* `dualSetup_nonvacuous`: non-vacuity of `FixedWeight.DualSetup` (unconditional witness at
  `virasoroProblem`).
* Virasoro instances `virasoro_lowerBoundInput`, `virasoro_corollary_E1_exact_gap`,
  `virasoro_corollary_E1_lower_bound`, `virasoro_corollary_E1`, and legacy `_of_YV` bridges.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: Airy threshold `T_*` and named threshold-bound inputs -/

/-- The Airy threshold `T_*(c̃) = ξ̄ c̃ + A_opt c̃^{1/3}` (`dual_spectrum.tex`). -/
noncomputable def TStar (cTilde : ℝ) : ℝ :=
  xiBar * cTilde + Aopt * cTilde ^ ((1 : ℝ) / 3)

lemma TStar_add_div_twelve (cTilde : ℝ) :
    cTilde / 12 + TStar cTilde = cTilde / lambdaV + Aopt * cTilde ^ ((1 : ℝ) / 3) := by
  unfold TStar
  rw [show cTilde / lambdaV = xiBar * cTilde + cTilde / 12 by
    rw [xiBar_eq_inv_lambdaV_sub]; ring]
  ring

/-- Abstract threshold lower-bound predicate `T(c̃) ≥ T_*(c̃) - D_-` for `c̃ ≥ c₁`. -/
def ThresholdLowerBoundAt (T : ℝ → ℝ) (shift : ℝ) : Prop :=
  ∃ c₁ D_minus : ℝ, max 1 (12 * shift) ≤ c₁ ∧ 0 ≤ D_minus ∧
    ∀ {cTilde : ℝ}, c₁ ≤ cTilde → TStar cTilde - D_minus ≤ T cTilde

/-- **Theorem W1'(1) (`lower_o1_two_edge.tex`, `wone:genlower(1)`)**:
for a fixed-weight problem `prob`, there exist `c₁ ≥ max 1 (12 S)` and `D_- ≥ 0` such that
`T_V(c̃) ≥ T_*(c̃) - D_-` for all `c̃ ≥ c₁`. (Proved for every `prob` by
`FixedWeightBand.fixedWeightLowerBoundInput_of_problem`.) -/
def FixedWeightLowerBoundInput (prob : FixedWeightProblem) : Prop :=
  ThresholdLowerBoundAt prob.T_V prob.totalShift

/-- Abstract threshold upper-bound predicate `T(c̃) ≤ T_*(c̃) + D_+` for `c̃ ≥ c₂`. -/
def ThresholdUpperBoundAt (T : ℝ → ℝ) (shift : ℝ) : Prop :=
  ∃ c₂ D_plus : ℝ, max 1 (12 * shift) ≤ c₂ ∧ 0 ≤ D_plus ∧
    ∀ {cTilde : ℝ}, c₂ ≤ cTilde → T cTilde ≤ TStar cTilde + D_plus

/-- **Unproved input (Theorem C15 / Theorem ctu.5, `thm:fixed-weight-expansion`)**:
for a fixed-weight problem `prob`, there exist `c₂ ≥ max 1 (12 S)` and `D_+ ≥ 0` such that
`T_V(c̃) ≤ T_*(c̃) + D_+` for all `c̃ ≥ c₂`. (Proved for `virasoroProblem` by `Upper.Ramped.theoremC15UpperInput_virasoro`, the `O(1)` upper
half via Lemma U* of `n2_ramped_comb.tex` `rem:thmU`; for every `prob` with `prob.w = 1` by `Upper.Ramped.theoremC15UpperInput_prob`; open for `w > 1`.) -/
def TheoremC15UpperInput (prob : FixedWeightProblem) : Prop :=
  ThresholdUpperBoundAt prob.T_V prob.totalShift

/-- Weak lower-bound predicate `T(c̃) ≥ ξ̄ c̃ - C_A c̃^{1/3}` for `c̃ ≥ c₁` (Theorem A form). -/
def WeakThresholdLowerBoundAt (T : ℝ → ℝ) (shift : ℝ) : Prop :=
  ∃ c₁ C_A : ℝ, max 1 (12 * shift) ≤ c₁ ∧ 0 < C_A ∧
    ∀ {cTilde : ℝ}, c₁ ≤ cTilde → xiBar * cTilde - C_A * cTilde ^ ((1 : ℝ) / 3) ≤ T cTilde

/-- Non-vacuity of `ThresholdLowerBoundAt`: witnessed by `T = TStar`. -/
theorem thresholdLowerBoundAt_nonvacuous :
    ∃ (T : ℝ → ℝ) (shift : ℝ), 0 ≤ shift ∧ ThresholdLowerBoundAt T shift :=
  ⟨TStar, 0, le_rfl, 1, 0, by norm_num, le_rfl, fun _ => by linarith⟩

/-- Non-vacuity of `ThresholdUpperBoundAt`: witnessed by `T = TStar`. -/
theorem thresholdUpperBoundAt_nonvacuous :
    ∃ (T : ℝ → ℝ) (shift : ℝ), 0 ≤ shift ∧ ThresholdUpperBoundAt T shift :=
  ⟨TStar, 0, le_rfl, 1, 0, by norm_num, le_rfl, fun _ => by linarith⟩

/-- Unconditional witness of `WeakThresholdLowerBoundAt` at `virasoroProblem.T_V` via Theorem A. -/
theorem weakThresholdLowerBound_virasoro :
    WeakThresholdLowerBoundAt virasoroProblem.T_V virasoroProblem.totalShift := by
  obtain ⟨C_A, c_A, hCA, hc_A, hTV⟩ := Integration.theoremA_T_V
  refine ⟨c_A, C_A, ?_, hCA, fun hc => hTV hc⟩
  rw [virasoroProblem_totalShift]
  exact max_le (by linarith) (by linarith)

/-- Unconditional witness of `FixedWeightLowerBoundInput` for `virasoroProblem` via
`Contour.theoremJ_T_V` (Theorem J / Theorem W1'(1)). -/
theorem virasoro_lowerBoundInput :
    FixedWeightLowerBoundInput virasoroProblem := by
  obtain ⟨c_2, C, hc2, hC, hTV⟩ := Contour.theoremJ_T_V
  refine ⟨c_2, C, ?_, hC, fun {cTilde} hc => ?_⟩
  · have hc24 : 24 ≤ c_2 :=
      ((by norm_num : (24 : ℝ) ≤ 10000).trans ConcreteBootstrap.virasoroCQEnv_ge).trans hc2
    rw [virasoroProblem_totalShift]
    exact max_le (by linarith) (by linarith)
  · exact hTV hc

/-- Bridge from `ConcreteBootstrap.YVInput` + `theoremJ_T_V` to `FixedWeightLowerBoundInput`
for `virasoroProblem`. -/
theorem virasoro_lowerBoundInput_of_YV (hYV : ConcreteBootstrap.YVInput) :
    FixedWeightLowerBoundInput virasoroProblem := by
  obtain ⟨c_2, C, hc2, hC, hTV⟩ := ConcreteBootstrap.theoremJ_T_V hYV
  refine ⟨c_2, C, ?_, hC, fun {cTilde} hc => ?_⟩
  · have hc24 : 24 ≤ c_2 :=
      ((by norm_num : (24 : ℝ) ≤ 10000).trans ConcreteBootstrap.virasoroCQEnv_ge).trans hc2
    rw [virasoroProblem_totalShift]
    exact max_le (by linarith) (by linarith)
  · exact hTV hc

/-! ### Section 2: Unconditional exact gap and Corollary E1 (`ds:E1`) -/

/-- **Corollary E1 (exact gap)** for every fixed weight `(w, Q)`: whenever `c̃ > 0`, `c̃ ≥ 12 S`,
and `T_V(c̃) > 0`, there is a crossing measure `ν_*` supported on `[T_V(c̃), ∞)` charging every
`[T_V(c̃), T_V(c̃) + ε)` (gap exactly `T_V(c̃)`), so `Δ_best(c̃) = c̃/12 + T_V(c̃)` is attained. -/
theorem corollary_E1_exact_gap (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) (hTV : 0 < prob.T_V cTilde) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Iio (prob.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V cTilde + ε))) ∧
      prob.Delta_best cTilde = cTilde / 12 + prob.T_V cTilde := by
  obtain ⟨β₀, hβ₀, hβ₀2, hT⟩ := exists_beta0 prob.w (half_pos hTV)
  have S : DualSetup prob cTilde β₀ (prob.T_V cTilde / 2) :=
    ⟨hc_pos, hc, hβ₀, hβ₀2, hT, half_pos hTV, by linarith⟩
  obtain ⟨meas, h1, h2, _⟩ := theorem_E_c prob S
  exact ⟨meas, h1, h2, rfl⟩

/-- Positivity of `ξ̄ c̃ - C_A c̃^{1/3}` for large `c̃`. -/
private lemma xiBar_sub_pos_of_large {C_A : ℝ} (hCA : 0 < C_A) {cTilde : ℝ}
    (hc : (C_A / xiBar + 1) ^ 3 ≤ cTilde) :
    0 < xiBar * cTilde - C_A * cTilde ^ ((1 : ℝ) / 3) := by
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  set M : ℝ := C_A / xiBar + 1 with hM
  have hM1 : 1 < M := by have : 0 < C_A / xiBar := div_pos hCA hxi; linarith
  have hc0 : 0 < cTilde := lt_of_lt_of_le (by positivity) hc
  set u : ℝ := cTilde ^ ((1 : ℝ) / 3) with hu
  have hu3 : u ^ 3 = cTilde := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hupos : 0 < u := Real.rpow_pos_of_pos hc0 _
  have hMu : M ≤ u := by
    by_contra hlt
    push Not at hlt
    have : u ^ 3 < M ^ 3 := pow_lt_pow_left₀ hlt hupos.le (by norm_num)
    linarith
  have hCx : C_A / xiBar < u := by linarith
  have hCx' : C_A < xiBar * u := by rwa [div_lt_iff₀ hxi, mul_comm] at hCx
  rw [← hu3]
  have hu1 : 1 ≤ u := by linarith
  have h2 : xiBar * u ≤ xiBar * u ^ 2 := by
    have : u ≤ u ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hxi.le
  have h3 : C_A < xiBar * u ^ 2 := lt_of_lt_of_le hCx' h2
  have : 0 < u * (xiBar * u ^ 2 - C_A) := mul_pos hupos (by linarith)
  nlinarith

/-- Positivity of `T_*(c̃) - D_-` for large `c̃`. -/
private lemma TStar_sub_pos_of_large {D_minus : ℝ} {cTilde : ℝ}
    (hc : max 1 (D_minus / xiBar + 1) ≤ cTilde) :
    0 < TStar cTilde - D_minus := by
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  have hc1 : 1 ≤ cTilde := (le_max_left _ _).trans hc
  have hc2 : D_minus / xiBar + 1 ≤ cTilde := (le_max_right _ _).trans hc
  have h0 : D_minus < xiBar * cTilde := by
    have hlt : D_minus / xiBar < cTilde := by linarith
    rwa [div_lt_iff₀ hxi, mul_comm] at hlt
  have hA : 0 ≤ Aopt * cTilde ^ ((1 : ℝ) / 3) := by
    have hAopt : 0 ≤ Aopt := by unfold Aopt; exact mul_nonneg cStar_pos.le (abs_nonneg _)
    positivity
  unfold TStar
  linarith

/-- **Corollary E1 from a weak lower bound**: for any `(w, Q)` satisfying
`WeakThresholdLowerBoundAt prob.T_V prob.totalShift`, for all sufficiently large `c̃` one has
`0 < ξ̄ c̃ - C_A c̃^{1/3} ≤ T_V(c̃)` and a crossing measure attaining gap `T_V(c̃)`. -/
theorem corollary_E1_of_weak_lower_bound (prob : FixedWeightProblem)
    (hLo : WeakThresholdLowerBoundAt prob.T_V prob.totalShift) :
    ∃ C_A c₀ : ℝ, 0 < C_A ∧ max 1 (12 * prob.totalShift) ≤ c₀ ∧ ∀ {cTilde : ℝ}, c₀ ≤ cTilde →
      0 < xiBar * cTilde - C_A * cTilde ^ ((1 : ℝ) / 3) ∧
      xiBar * cTilde - C_A * cTilde ^ ((1 : ℝ) / 3) ≤ prob.T_V cTilde ∧
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (Iio (prob.T_V cTilde)) = 0 ∧
        ∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V cTilde + ε)) := by
  obtain ⟨c₁, C_A, hc₁_ge, hCA, hTV⟩ := hLo
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  refine ⟨C_A, max c₁ ((C_A / xiBar + 1) ^ 3), hCA, hc₁_ge.trans (le_max_left _ _),
    fun {cTilde} hc => ?_⟩
  have hcA : c₁ ≤ cTilde := (le_max_left _ _).trans hc
  have hcM : (C_A / xiBar + 1) ^ 3 ≤ cTilde := (le_max_right _ _).trans hc
  have hpos := xiBar_sub_pos_of_large hCA hcM
  have hbound := hTV hcA
  have hTVpos : 0 < prob.T_V cTilde := lt_of_lt_of_le hpos hbound
  have hc_pos : 0 < cTilde := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₁_ge.trans hcA))
  have hshift : 12 * prob.totalShift ≤ cTilde := (le_max_right _ _).trans (hc₁_ge.trans hcA)
  obtain ⟨meas, h1, h2, _⟩ := corollary_E1_exact_gap prob hc_pos hshift hTVpos
  exact ⟨hpos, hbound, meas, h1, h2⟩

/-- **Corollary E1 (`dual_spectrum.tex`, `ds:E1`)** at general `(w, Q)`, proved given the
threshold lower bound `FixedWeightLowerBoundInput prob` (Theorem W1'(1)) and upper bound
`TheoremC15UpperInput prob` (Theorem C15 / ctu.5):
for all sufficiently large `c̃`,
* `0 < T_V(c̃)` and `|T_V(c̃) - T_*(c̃)| ≤ C` (equivalently
  `|Δ_best(c̃) - (c̃ / Λ_V + A_opt c̃^{1/3})| ≤ C`);
* there is a crossing measure `ν_*` with gap `min supp ν_* = T_V(c̃)`, attaining `Δ_best(c̃)`;
* for every sequence `c̃_j → ∞`, `(T_V(c̃_j) - T_*(c̃_j)) / c̃_j^{1/3} → 0` (in particular
  `liminf_j (τ_j - T_*(c̃_j)) / c̃_j^{1/3} ≥ 0`, so hypothesis `(Gap)` of `sr:Sigma0` and
  `sr:Sigma` holds for `ν_*(c̃_j)`). -/
theorem corollary_E1 (prob : FixedWeightProblem)
    (hLo : FixedWeightLowerBoundInput prob) (hHi : TheoremC15UpperInput prob) :
    ∃ c₀ C : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧ 0 ≤ C ∧
      (∀ {cTilde : ℝ}, c₀ ≤ cTilde →
        0 < prob.T_V cTilde ∧
        |prob.T_V cTilde - TStar cTilde| ≤ C ∧
        |prob.Delta_best cTilde - (cTilde / lambdaV + Aopt * cTilde ^ ((1 : ℝ) / 3))| ≤ C ∧
        ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
          meas.ν (Iio (prob.T_V cTilde)) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V cTilde + ε))) ∧
          prob.Delta_best cTilde = cTilde / 12 + prob.T_V cTilde) ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (prob.T_V (cSeq j) - TStar (cSeq j)) / (cSeq j) ^ ((1 : ℝ) / 3))
          atTop (𝓝 0)) := by
  obtain ⟨c₁, D_minus, hc₁, hDm, hlo⟩ := hLo
  obtain ⟨c₂, D_plus, hc₂, hDp, hhi⟩ := hHi
  let c₀ : ℝ := max (max c₁ c₂) (D_minus / xiBar + 1)
  let C : ℝ := max D_minus D_plus
  have hc₀_ge : max 1 (12 * prob.totalShift) ≤ c₀ :=
    hc₁.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hC_nn : 0 ≤ C := le_max_of_le_left hDm
  refine ⟨c₀, C, hc₀_ge, hC_nn, fun {cTilde} hc => ?_, fun cSeq hcSeq => ?_⟩
  · have hc1 : c₁ ≤ cTilde := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
    have hc2 : c₂ ≤ cTilde := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
    have hc1_ge1 : 1 ≤ cTilde := (le_max_left _ _).trans (hc₀_ge.trans hc)
    have hc_pos : 0 < cTilde := lt_of_lt_of_le zero_lt_one hc1_ge1
    have hshift : 12 * prob.totalShift ≤ cTilde := (le_max_right _ _).trans (hc₀_ge.trans hc)
    have hpos_lo : 0 < TStar cTilde - D_minus :=
      TStar_sub_pos_of_large (max_le hc1_ge1 ((le_max_right _ _).trans hc))
    have hTV_lo : TStar cTilde - D_minus ≤ prob.T_V cTilde := hlo hc1
    have hTV_hi : prob.T_V cTilde ≤ TStar cTilde + D_plus := hhi hc2
    have hTV_pos : 0 < prob.T_V cTilde := lt_of_lt_of_le hpos_lo hTV_lo
    have hdiff : |prob.T_V cTilde - TStar cTilde| ≤ C := by
      rw [abs_le]
      constructor
      · linarith [le_max_left D_minus D_plus]
      · linarith [le_max_right D_minus D_plus]
    have hDelta : |prob.Delta_best cTilde - (cTilde / lambdaV + Aopt * cTilde ^ ((1 : ℝ) / 3))| ≤ C := by
      unfold FixedWeightProblem.Delta_best
      rw [← TStar_add_div_twelve,
        show cTilde / 12 + prob.T_V cTilde - (cTilde / 12 + TStar cTilde) =
          prob.T_V cTilde - TStar cTilde by ring]
      exact hdiff
    obtain ⟨meas, h1, h2, h3⟩ := corollary_E1_exact_gap prob hc_pos hshift hTV_pos
    exact ⟨hTV_pos, hdiff, hDelta, meas, h1, h2, h3⟩
  · have hpow_tend : Tendsto (fun j => C / (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
      have hr : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 3)) atTop atTop :=
        tendsto_rpow_atTop (by norm_num)
      have hc_rpow : Tendsto (fun j => (cSeq j) ^ ((1 : ℝ) / 3)) atTop atTop := hr.comp hcSeq
      exact tendsto_const_nhds.div_atTop hc_rpow
    have hneg_tend : Tendsto (fun j => -(C / (cSeq j) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
      simpa using hpow_tend.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg_tend hpow_tend ?_ ?_
    · filter_upwards [hcSeq.eventually (eventually_ge_atTop c₀)] with j hj
      have hc1 : c₁ ≤ cSeq j := ((le_max_left _ _).trans (le_max_left _ _)).trans hj
      have hc_pos : 0 < cSeq j :=
        lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₀_ge.trans hj))
      have hden_pos : 0 < (cSeq j) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
      have hlo_j : -C ≤ prob.T_V (cSeq j) - TStar (cSeq j) := by
        linarith [hlo hc1, le_max_left D_minus D_plus]
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hlo_j hden_pos.le
    · filter_upwards [hcSeq.eventually (eventually_ge_atTop c₀)] with j hj
      have hc2 : c₂ ≤ cSeq j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
      have hc_pos : 0 < cSeq j :=
        lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₀_ge.trans hj))
      have hden_pos : 0 < (cSeq j) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
      have hhi_j : prob.T_V (cSeq j) - TStar (cSeq j) ≤ C := by
        linarith [hhi hc2, le_max_right D_minus D_plus]
      exact div_le_div_of_nonneg_right hhi_j hden_pos.le

/-! ### Section 3: Non-vacuity and Virasoro instances -/

/-- Non-vacuity of `FixedWeight.DualSetup`: witnessed unconditionally at `virasoroProblem`. -/
theorem dualSetup_nonvacuous :
    ∃ (prob : FixedWeightProblem) (cTilde β₀ T₀ : ℝ), DualSetup prob cTilde β₀ T₀ := by
  obtain ⟨cTilde, β₀, T₀, hS⟩ := Duality.dualSetup_nonvacuous
  exact ⟨virasoroProblem, cTilde, β₀, T₀, DualSetup.of_virasoro hS⟩

/-- Conditional `DualSetup` constructor from `FixedWeightLowerBoundInput prob`. -/
theorem dualSetup_of_lowerBound (prob : FixedWeightProblem) (hLo : FixedWeightLowerBoundInput prob) :
    ∃ cTilde β₀ T₀ : ℝ, DualSetup prob cTilde β₀ T₀ := by
  obtain ⟨c₁, D_minus, hc₁, hDm, hlo⟩ := hLo
  let cTilde : ℝ := max c₁ (D_minus / xiBar + 1)
  have hc1 : c₁ ≤ cTilde := le_max_left _ _
  have hc1_ge1 : 1 ≤ cTilde := (le_max_left _ _).trans (hc₁.trans hc1)
  have hc_pos : 0 < cTilde := lt_of_lt_of_le zero_lt_one hc1_ge1
  have hshift : 12 * prob.totalShift ≤ cTilde := (le_max_right _ _).trans (hc₁.trans hc1)
  have hTV : 0 < prob.T_V cTilde :=
    lt_of_lt_of_le (TStar_sub_pos_of_large (max_le hc1_ge1 (le_max_right _ _))) (hlo hc1)
  obtain ⟨β₀, hβ₀, hβ₀2, hT⟩ := exists_beta0 prob.w (half_pos hTV)
  exact ⟨cTilde, β₀, prob.T_V cTilde / 2, hc_pos, hshift, hβ₀, hβ₀2, hT, half_pos hTV, by linarith⟩

/-- Spinless Virasoro exact-gap corollary, re-derived from `FixedWeight.corollary_E1_exact_gap`. -/
theorem virasoro_corollary_E1_exact_gap {cTilde : ℝ}
    (hc : 12 * virasoroProblem.totalShift ≤ cTilde) (hTV : 0 < virasoroProblem.T_V cTilde) :
    ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      meas.ν (Iio (virasoroProblem.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V cTilde + ε))) ∧
      virasoroProblem.Delta_best cTilde = cTilde / 12 + virasoroProblem.T_V cTilde :=
  corollary_E1_exact_gap virasoroProblem
    (by have := hc; rw [virasoroProblem_totalShift] at this; linarith) hc hTV

/-- Spinless Virasoro unconditional lower-bound form, re-derived from
`FixedWeight.corollary_E1_of_weak_lower_bound`. -/
theorem virasoro_corollary_E1_lower_bound :
    ∃ C_A c₁ : ℝ, 0 < C_A ∧ 24 ≤ c₁ ∧ ∀ {c' : ℝ}, c₁ ≤ c' →
      0 < xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ∧
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_V c' ∧
      ∃ meas : AdmissibleCrossingMeasure virasoroProblem (c' / 12),
        meas.ν (Iio (virasoroProblem.T_V c')) = 0 ∧
        ∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V c' + ε)) := by
  obtain ⟨C_A, c₀, hCA, hc₀, hall⟩ :=
    corollary_E1_of_weak_lower_bound virasoroProblem weakThresholdLowerBound_virasoro
  have hc24 : 24 ≤ c₀ := by
    have := (le_max_right (1 : ℝ) (12 * virasoroProblem.totalShift)).trans hc₀
    rw [virasoroProblem_totalShift] at this
    linarith
  exact ⟨C_A, c₀, hCA, hc24, fun hc => hall hc⟩

/-- Spinless Virasoro full Corollary E1 given `TheoremC15UpperInput virasoroProblem`
(with the lower bound `FixedWeightLowerBoundInput virasoroProblem` supplied unconditionally by
`virasoro_lowerBoundInput`). -/
theorem virasoro_corollary_E1 (hC15 : TheoremC15UpperInput virasoroProblem) :
    ∃ c₀ C : ℝ, 24 ≤ c₀ ∧ 0 ≤ C ∧
      (∀ {c' : ℝ}, c₀ ≤ c' →
        0 < virasoroProblem.T_V c' ∧
        |virasoroProblem.T_V c' - TStar c'| ≤ C ∧
        |virasoroProblem.Delta_best c' - (c' / lambdaV + Aopt * c' ^ ((1 : ℝ) / 3))| ≤ C ∧
        ∃ meas : AdmissibleCrossingMeasure virasoroProblem (c' / 12),
          meas.ν (Iio (virasoroProblem.T_V c')) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V c' + ε))) ∧
          virasoroProblem.Delta_best c' = c' / 12 + virasoroProblem.T_V c') ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (virasoroProblem.T_V (cSeq j) - TStar (cSeq j)) /
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) := by
  obtain ⟨c₀, C, hc₀, hC, hall, hlim⟩ :=
    corollary_E1 virasoroProblem virasoro_lowerBoundInput hC15
  have hc24 : 24 ≤ c₀ := by
    have := (le_max_right (1 : ℝ) (12 * virasoroProblem.totalShift)).trans hc₀
    rw [virasoroProblem_totalShift] at this
    linarith
  exact ⟨c₀, C, hc24, hC, hall, hlim⟩

/-- Spinless Virasoro full Corollary E1 given `ConcreteBootstrap.YVInput` and
`TheoremC15UpperInput virasoroProblem`. -/
theorem virasoro_corollary_E1_of_YV (hYV : ConcreteBootstrap.YVInput)
    (hC15 : TheoremC15UpperInput virasoroProblem) :
    ∃ c₀ C : ℝ, 24 ≤ c₀ ∧ 0 ≤ C ∧
      (∀ {c' : ℝ}, c₀ ≤ c' →
        0 < virasoroProblem.T_V c' ∧
        |virasoroProblem.T_V c' - TStar c'| ≤ C ∧
        |virasoroProblem.Delta_best c' - (c' / lambdaV + Aopt * c' ^ ((1 : ℝ) / 3))| ≤ C ∧
        ∃ meas : AdmissibleCrossingMeasure virasoroProblem (c' / 12),
          meas.ν (Iio (virasoroProblem.T_V c')) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V c' + ε))) ∧
          virasoroProblem.Delta_best c' = c' / 12 + virasoroProblem.T_V c') ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (virasoroProblem.T_V (cSeq j) - TStar (cSeq j)) /
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) := by
  obtain ⟨c₀, C, hc₀, hC, hall, hlim⟩ :=
    corollary_E1 virasoroProblem (virasoro_lowerBoundInput_of_YV hYV) hC15
  have hc24 : 24 ≤ c₀ := by
    have := (le_max_right (1 : ℝ) (12 * virasoroProblem.totalShift)).trans hc₀
    rw [virasoroProblem_totalShift] at this
    linarith
  exact ⟨c₀, C, hc24, hC, hall, hlim⟩

/-! ### Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.corollary_E1_exact_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.corollary_E1_exact_gap

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.corollary_E1_of_weak_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.corollary_E1_of_weak_lower_bound

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.corollary_E1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.corollary_E1

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.thresholdLowerBoundAt_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.thresholdLowerBoundAt_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.thresholdUpperBoundAt_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.thresholdUpperBoundAt_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.weakThresholdLowerBound_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.weakThresholdLowerBound_virasoro

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.dualSetup_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.dualSetup_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.virasoro_lowerBoundInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.virasoro_lowerBoundInput

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.virasoro_corollary_E1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.virasoro_corollary_E1

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.virasoro_corollary_E1_of_YV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.virasoro_corollary_E1_of_YV

end FormalResearch.ModularBootstrap.FixedWeight