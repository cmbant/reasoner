module

public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# Fixed-weight Corollary E1 with an `o(c^{1/3})` upper bound (`dual_spectrum.tex`, `ds:E1`)

`FixedWeight.corollary_E1` assumes the O(1) upper bound `TheoremC15UpperInput prob`
(`T_V(c) ≤ T_*(c) + D_+`). This module weakens that input to the `o(c^{1/3})` upper bound
`ThresholdUpperLittleOAt prob.T_V prob.totalShift`: for every `δ > 0`, eventually
`T_V(c) ≤ T_*(c) + δ c^{1/3}`. Everything else is unchanged; the lower bound is still
`FixedWeightLowerBoundInput prob` (Theorem W1'(1)).

* `ThresholdUpperLittleOAt`: the named `o(c^{1/3})` upper-bound predicate, non-vacuous by
  `thresholdUpperLittleOAt_nonvacuous` (witness `T = T_*`, shift `0`).
* `ThresholdUpperBoundAt.littleO`: an O(1) upper bound implies the `o(c^{1/3})` one, so
  `corollary_E1_littleO` strictly generalises `corollary_E1` in its upper-bound hypothesis.
* `corollary_E1_littleO` (`ds:E1` without the O(1) upper bound): given the lower bound with
  constant `D_-` and the `o(c^{1/3})` upper bound, for all sufficiently large `c`:
  `0 < T_V(c)`, a crossing measure `ν` with `min supp ν = T_V(c)` attaining `Δ_best(c)`; for every
  `δ > 0` eventually `|T_V(c) - T_*(c)| ≤ D_- + δ c^{1/3}` and the same bound for
  `|Δ_best(c) - (c/Λ_V + A_opt c^{1/3})|`; and `(T_V(c_j) - T_*(c_j)) / c_j^{1/3} → 0` along every
  `c_j → ∞`, which is hypothesis `(Gap)` of `sr:Sigma0`, `sr:Sigma` (`gapCondition_of_tendsto`).
* `virasoro_corollary_E1_littleO`: the same statement at `virasoroProblem`, with the lower bound
  supplied unconditionally by `virasoro_lowerBoundInput` (Theorem J).

Claim classes: all statements are proved (unconditional apart from the named upper-bound
hypothesis `ThresholdUpperLittleOAt`, which is an explicit argument of `corollary_E1_littleO`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: the `o(c^{1/3})` upper-bound predicate -/

/-- Abstract `o(c^{1/3})` upper-bound predicate: for every `δ > 0` there is `c₂ ≥ max 1 (12 S)`
with `T(c) ≤ T_*(c) + δ c^{1/3}` for all `c ≥ c₂`. -/
def ThresholdUpperLittleOAt (T : ℝ → ℝ) (shift : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c₂ : ℝ, max 1 (12 * shift) ≤ c₂ ∧
    ∀ {c : ℝ}, c₂ ≤ c → T c ≤ TStar c + δ * c ^ ((1 : ℝ) / 3)

/-- Non-vacuity of `ThresholdUpperLittleOAt`: witnessed by `T = T_*` and shift `0`
(there `T_* ≤ T_* + δ c^{1/3}` holds for every `δ > 0`). -/
theorem thresholdUpperLittleOAt_nonvacuous :
    ∃ (T : ℝ → ℝ) (shift : ℝ), 0 ≤ shift ∧ ThresholdUpperLittleOAt T shift := by
  refine ⟨TStar, 0, le_rfl, fun δ hδ => ⟨1, ?_, fun {c} hc => ?_⟩⟩
  · norm_num
  · have hc0 : 0 ≤ c := by linarith
    have := mul_nonneg hδ.le (Real.rpow_nonneg hc0 ((1 : ℝ) / 3))
    linarith

/-- An O(1) upper bound `T(c) ≤ T_*(c) + D_+` implies the `o(c^{1/3})` upper bound: for
`δ > 0` take `c₂' = max c₂ ((D_+/δ)^3)`, so that `D_+ ≤ δ c^{1/3}` for `c ≥ c₂'`. -/
theorem ThresholdUpperBoundAt.littleO {T : ℝ → ℝ} {shift : ℝ}
    (h : ThresholdUpperBoundAt T shift) : ThresholdUpperLittleOAt T shift := by
  obtain ⟨c₂, D_plus, hc₂, hD, hhi⟩ := h
  intro δ hδ
  refine ⟨max c₂ ((D_plus / δ) ^ 3), hc₂.trans (le_max_left _ _), fun {c} hc => ?_⟩
  have hc2 : c₂ ≤ c := (le_max_left _ _).trans hc
  have hc3 : (D_plus / δ) ^ 3 ≤ c := (le_max_right _ _).trans hc
  have hx : 0 ≤ D_plus / δ := div_nonneg hD hδ.le
  have hc0 : 0 ≤ c := le_trans (pow_nonneg hx 3) hc3
  have hu0 : 0 ≤ c ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc0 _
  have hu3 : (c ^ ((1 : ℝ) / 3)) ^ 3 = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
  have hcube : D_plus / δ ≤ c ^ ((1 : ℝ) / 3) := by
    by_contra hlt
    push Not at hlt
    have h3 : (c ^ ((1 : ℝ) / 3)) ^ 3 < (D_plus / δ) ^ 3 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
    linarith
  have hD' : D_plus ≤ δ * c ^ ((1 : ℝ) / 3) := by
    have h1 : D_plus ≤ c ^ ((1 : ℝ) / 3) * δ := (div_le_iff₀ hδ).mp hcube
    linarith [mul_comm (c ^ ((1 : ℝ) / 3)) δ]
  have := hhi hc2
  linarith

/-! ### Section 2: a private copy of the positivity helper of `OptimalMeasure` -/

/-- Positivity of `T_*(c) - D_-` for large `c` (the helper `TStar_sub_pos_of_large` of
`FixedWeight.OptimalMeasure` is private to that file, so it is restated here). -/
private lemma TStar_sub_pos_of_large_littleO {D_minus : ℝ} {c : ℝ}
    (hc : max 1 (D_minus / xiBar + 1) ≤ c) :
    0 < TStar c - D_minus := by
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc2 : D_minus / xiBar + 1 ≤ c := (le_max_right _ _).trans hc
  have h0 : D_minus < xiBar * c := by
    have hlt : D_minus / xiBar < c := by linarith
    rwa [div_lt_iff₀ hxi, mul_comm] at hlt
  have hA : 0 ≤ Aopt * c ^ ((1 : ℝ) / 3) := by
    have hAopt : 0 ≤ Aopt := by unfold Aopt; exact mul_nonneg cStar_pos.le (abs_nonneg _)
    positivity
  unfold TStar
  linarith

/-! ### Section 3: Corollary E1 with the `o(c^{1/3})` upper bound -/

/-- **Corollary E1 without the O(1) upper bound** (`dual_spectrum.tex`, `ds:E1`), at general
`(w, Q)`: proved given the threshold lower bound `FixedWeightLowerBoundInput prob` (Theorem W1'(1),
with constant `D_-`) and the `o(c^{1/3})` upper bound `ThresholdUpperLittleOAt prob.T_V`.
Set `D := D_-`. For all sufficiently large `c`:
* `0 < T_V(c)`, and there is a crossing measure `ν` with `ν(-∞, T_V(c)) = 0`,
  `ν(-∞, T_V(c) + ε) > 0` for all `ε > 0` (gap exactly `T_V(c)`), attaining `Δ_best(c)`;
* for every `δ > 0`, eventually `|T_V(c) - T_*(c)| ≤ D + δ c^{1/3}` and
  `|Δ_best(c) - (c/Λ_V + A_opt c^{1/3})| ≤ D + δ c^{1/3}`;
* for every sequence `c_j → ∞`, `(T_V(c_j) - T_*(c_j)) / c_j^{1/3} → 0`, so the (Gap) condition of
  `sr:Sigma0`, `sr:Sigma` holds (`Upper.Rigidity.gapCondition_of_tendsto`). -/
theorem corollary_E1_littleO (prob : FixedWeightProblem)
    (hLo : FixedWeightLowerBoundInput prob) (hHi : ThresholdUpperLittleOAt prob.T_V prob.totalShift) :
    ∃ c₀ D : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧ 0 ≤ D ∧
      (∀ {c : ℝ}, c₀ ≤ c →
        0 < prob.T_V c ∧
        ∃ meas : AdmissibleCrossingMeasure prob (c / 12),
          meas.ν (Iio (prob.T_V c)) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V c + ε))) ∧
          prob.Delta_best c = c / 12 + prob.T_V c) ∧
      (∀ δ : ℝ, 0 < δ → ∃ c₁ : ℝ, ∀ {c : ℝ}, c₁ ≤ c →
        |prob.T_V c - TStar c| ≤ D + δ * c ^ ((1 : ℝ) / 3) ∧
        |prob.Delta_best c - (c / lambdaV + Aopt * c ^ ((1 : ℝ) / 3))| ≤
          D + δ * c ^ ((1 : ℝ) / 3)) ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (prob.T_V (cSeq j) - TStar (cSeq j)) / (cSeq j) ^ ((1 : ℝ) / 3))
          atTop (𝓝 0)) := by
  obtain ⟨c₁, D_minus, hc₁, hDm, hlo⟩ := hLo
  refine ⟨max c₁ (D_minus / xiBar + 1), D_minus, hc₁.trans (le_max_left _ _), hDm,
    fun {c} hc => ?_, fun δ hδ => ?_, fun cSeq hcSeq => ?_⟩
  · -- exact gap, as in `corollary_E1`; only the lower bound is used
    have hc1 : c₁ ≤ c := (le_max_left _ _).trans hc
    have hc1_ge1 : 1 ≤ c := (le_max_left _ _).trans (hc₁.trans hc1)
    have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc1_ge1
    have hshift : 12 * prob.totalShift ≤ c := (le_max_right _ _).trans (hc₁.trans hc1)
    have hpos_lo : 0 < TStar c - D_minus :=
      TStar_sub_pos_of_large_littleO (max_le hc1_ge1 ((le_max_right _ _).trans hc))
    have hTV_pos : 0 < prob.T_V c := lt_of_lt_of_le hpos_lo (hlo hc1)
    obtain ⟨meas, h1, h2, h3⟩ := corollary_E1_exact_gap prob hc_pos hshift hTV_pos
    exact ⟨hTV_pos, meas, h1, h2, h3⟩
  · -- the two-sided bound with the `δ c^{1/3}` error
    obtain ⟨c₂, -, hhi⟩ := hHi δ hδ
    refine ⟨max c₁ c₂, fun {c} hc => ?_⟩
    have hc1 : c₁ ≤ c := (le_max_left _ _).trans hc
    have hc2 : c₂ ≤ c := (le_max_right _ _).trans hc
    have hc1_ge1 : 1 ≤ c := (le_max_left _ _).trans (hc₁.trans hc1)
    have hc0 : 0 ≤ c := by linarith
    have hlo_c : TStar c - D_minus ≤ prob.T_V c := hlo hc1
    have hhi_c : prob.T_V c ≤ TStar c + δ * c ^ ((1 : ℝ) / 3) := hhi hc2
    have hδc : 0 ≤ δ * c ^ ((1 : ℝ) / 3) := mul_nonneg hδ.le (Real.rpow_nonneg hc0 _)
    have hdiff : |prob.T_V c - TStar c| ≤ D_minus + δ * c ^ ((1 : ℝ) / 3) := by
      rw [abs_le]; constructor <;> linarith
    refine ⟨hdiff, ?_⟩
    unfold FixedWeightProblem.Delta_best
    rw [← TStar_add_div_twelve,
      show c / 12 + prob.T_V c - (c / 12 + TStar c) = prob.T_V c - TStar c by ring]
    exact hdiff
  · -- `(T_V - T_*)/c^{1/3} → 0` along `c_j → ∞`
    have hr : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 3)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have hc_rpow : Tendsto (fun j => (cSeq j) ^ ((1 : ℝ) / 3)) atTop atTop := hr.comp hcSeq
    have hpow_tend : Tendsto (fun j => D_minus / (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hc_rpow
    have hneg_tend : Tendsto (fun j => -(D_minus / (cSeq j) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
      simpa using hpow_tend.neg
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [hneg_tend.eventually (lt_mem_nhds ha),
        hcSeq.eventually (eventually_ge_atTop (max c₁ 1))] with j hj hjc
      have hcj1 : c₁ ≤ cSeq j := (le_max_left _ _).trans hjc
      have hcj_ge1 : 1 ≤ cSeq j := (le_max_right _ _).trans hjc
      have hden : 0 < (cSeq j) ^ ((1 : ℝ) / 3) :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hcj_ge1) _
      have hlo_j : -D_minus ≤ prob.T_V (cSeq j) - TStar (cSeq j) := by
        linarith [hlo hcj1]
      have hlow : -(D_minus / (cSeq j) ^ ((1 : ℝ) / 3)) ≤
          (prob.T_V (cSeq j) - TStar (cSeq j)) / (cSeq j) ^ ((1 : ℝ) / 3) := by
        rw [← neg_div]
        exact div_le_div_of_nonneg_right hlo_j hden.le
      exact lt_of_lt_of_le hj hlow
    · intro b hb
      obtain ⟨c₂, -, hhi⟩ := hHi (b / 2) (half_pos hb)
      filter_upwards [hcSeq.eventually (eventually_ge_atTop (max (max c₁ c₂) 1))] with j hj
      have hcj2 : c₂ ≤ cSeq j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
      have hcj_ge1 : 1 ≤ cSeq j := (le_max_right _ _).trans hj
      have hden : 0 < (cSeq j) ^ ((1 : ℝ) / 3) :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hcj_ge1) _
      have hup : (prob.T_V (cSeq j) - TStar (cSeq j)) / (cSeq j) ^ ((1 : ℝ) / 3) ≤ b / 2 := by
        rw [div_le_iff₀ hden]
        linarith [hhi hcj2]
      exact lt_of_le_of_lt hup (by linarith)

/-- **Virasoro, Corollary E1 with the `o(c^{1/3})` upper bound**: at `virasoroProblem` the lower
bound is unconditional (`virasoro_lowerBoundInput`, Theorem J), so only the `o(c^{1/3})` upper
bound is an input. The threshold `c₀` is at least `24 = 12 · totalShift`. -/
theorem virasoro_corollary_E1_littleO
    (hHi : ThresholdUpperLittleOAt virasoroProblem.T_V virasoroProblem.totalShift) :
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
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) := by
  obtain ⟨c₀, D, hc₀, hD, hall, hδ, hlim⟩ :=
    corollary_E1_littleO virasoroProblem virasoro_lowerBoundInput hHi
  have hc24 : 24 ≤ c₀ := by
    have := (le_max_right (1 : ℝ) (12 * virasoroProblem.totalShift)).trans hc₀
    rw [virasoroProblem_totalShift] at this
    linarith
  exact ⟨c₀, D, hc24, hD, hall, hδ, hlim⟩

/-! ### Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.thresholdUpperLittleOAt_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.thresholdUpperLittleOAt_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.ThresholdUpperBoundAt.littleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.ThresholdUpperBoundAt.littleO

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.corollary_E1_littleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.corollary_E1_littleO

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.virasoro_corollary_E1_littleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.virasoro_corollary_E1_littleO

end FormalResearch.ModularBootstrap.FixedWeight
