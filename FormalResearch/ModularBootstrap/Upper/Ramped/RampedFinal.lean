module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedThreshold
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuum
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOne
public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignG
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# Lemma `U*` assembled: the `O(1)` upper bound `T_V(c̃) ≤ T_*(c̃) + D_+` for every weight-one problem

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), together with `upper_transfer.tex`
(`ut:Phi`, `ut:III`, `ut:V`).

* `rampedG P c'`: the test function `g = ½(h₀ - ĥ₀)` of the ramped design `D_*` at `d = rampedD P c'`
  (`pairOdd` of the comb profile and its Hankel transform).
* `rampedG_isFeasible_prob`, `threshold_le_rampedTstar_prob`, **`theoremC15UpperInput_prob`**: the general
  statements for every `prob` with `prob.w = 1` (vacuum from `rampedVacuum_prob`); the Virasoro forms below are
  their instances.
* `rampedG_isFeasible`: there is `P : RampedParams` such that, eventually in `c'`, `rampedG P c'` is feasible
  for `virasoroProblem` at `a = c'/12` and gap `T = t_*(P, c') + 1` (`IsFeasible`): membership from `ramped_k7`,
  `g ≥ 0` on `[t_* + 1, ∞)` from `rampedPositive_tstar` (`twoG = 2 g`, through `InnerCombHyp.edgeHankel_eq`) and
  `g_vac > 0` from `rampedVacuum`.
* `threshold_le_rampedTstar`: hence `T_V(c') ≤ t_*(P, c') + 1` for `c'` large.
* **`theoremC15UpperInput_virasoro`**: `T_V(c̃) ≤ T_*(c̃) + D_+` for `c̃` large, with
  `D_+ = 1 + (A_opt/|a_1|) M_0 + C` (`rampedThreshold`); this is `TheoremC15UpperInput virasoroProblem`.
* **`virasoro_corollary_E1_unconditional`**: the two-sided `O(1)` law `Δ_best = c/Λ_V + A_opt c^{1/3} + O(1)`,
  `T_V = T_* + O(1)`, with the extremal measure and the `(Gap)` clause (`virasoro_corollary_E1` with the
  input discharged).

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Assembly FormalResearch.Special

/-- The test function `g = ½(h₀ - ĥ₀)` of the ramped design `D_*` at `d = M_0 c'^{-1/3}`. -/
noncomputable def rampedG (P : RampedParams) (c' : ℝ) : ℝ → ℝ :=
  pairOdd (combProfile c' (rampedComb P (rampedD P c') c'))
    (hankelTransform 1 (combProfile c' (rampedComb P (rampedD P c') c')))

lemma rampedTstar_nonneg (P : RampedParams) {c' : ℝ} (hc' : 0 ≤ c') : 0 ≤ rampedTstar P c' := by
  unfold rampedTstar; positivity

/-- `twoG = 2 g` at `t = c' x²/3`, for the ramped design. -/
lemma rampedG_eq_twoG (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {d : ℝ}
    (hI : InnerCombHyp c' (rampedComb P d c'))
    {C : ℝ} (hdec : DecayBound c' C (combProfile c' (rampedComb P d c'))) {x : ℝ} (hx : 0 ≤ x)
    (hx0 : 0 < c' * x ^ 2 / 3) :
    twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x =
      2 * pairOdd (combProfile c' (rampedComb P d c'))
        (hankelTransform 1 (combProfile c' (rampedComb P d c'))) (c' * x ^ 2 / 3) := by
  have hedge := hI.edgeHankel_eq hc' hdec hx0
  have hh : designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') (x : ℂ) =
      ((combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3) : ℝ) : ℂ) := by
    have h1 := hI.combProfile_eq (s := c' * x ^ 2 / 3) hx0
    have h2 : √(3 * (c' * x ^ 2 / 3) / c') = x := by
      rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp, Real.sqrt_sq hx]
    unfold rampedComb at h1 ⊢
    rw [h2] at h1
    rw [← combH0_designComb]
    exact h1
  have e2 : edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c')
      (rampedEps P c')) (c' * x ^ 2 / 3) =
      ((hankelTransform 1 (combProfile c' (rampedComb P d c')) (c' * x ^ 2 / 3) : ℝ) : ℂ) := by
    rw [← combH0_designComb]
    exact hedge
  unfold twoG pairOdd
  rw [hh, e2]
  simp only [Complex.sub_re, Complex.ofReal_re]
  ring

/-- **Feasibility of the ramped design at the gap `t_* + 1`, every weight-one problem** (`rem:thmU`, Steps
(1)-(5)): there is `P` such that for `c'` large `g = ½(h₀ - ĥ₀)` of `D_*` is feasible for `prob` at `a = c'/12`
and `T = t_*(P, c') + 1`. -/
theorem rampedG_isFeasible_prob (prob : FixedWeightProblem) (hw : prob.w = 1) :
    ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop,
      0 < rampedTstar P c' + 1 ∧ prob.IsFeasible (c' / 12) (rampedTstar P c' + 1) (rampedG P c') := by
  obtain ⟨CI, Cmid, hCI, hCm, hpos⟩ := rampedPositive_tstar
  obtain ⟨M0, hM0, hvac⟩ := rampedVacuum_prob prob hw CI Cmid hCI hCm
  obtain ⟨K, hK, hk7⟩ := ramped_k7 hw
  obtain ⟨P, hP1, hP2, hP3⟩ : ∃ P : RampedParams, P.CI = CI ∧ P.Cmid = Cmid ∧ P.M0 = M0 :=
    ⟨⟨CI, Cmid, M0, hCI, hCm, hM0⟩, rfl, rfl, rfl⟩
  refine ⟨P, ?_⟩
  filter_upwards [hpos P hP1 hP2, hvac P hP1 hP2 hP3, hk7, ramped_phaseHyp,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    rampedD_mem P, eventually_gt_atTop (0 : ℝ)]
    with c' hP hV hK7 hph hin hd hc'
  have hd1 : rampedD P c' ≤ 1 := hd.2.trans rampedD0_le_one
  have hT0 : 0 < rampedTstar P c' + 1 := by
    have := rampedTstar_nonneg P hc'.le
    linarith
  refine ⟨hT0, ?_, hV, fun t ht => ?_⟩
  · obtain ⟨C, -, -, -, hT, -⟩ := hK7 P (rampedD P c') hd.1 hd1
    exact hT
  · have hPh := hph P (rampedD P c') hd.1 hd1
    have hI : InnerCombHyp c' (rampedComb P (rampedD P c') c') :=
      hin (nCap P c' + 6) (rampedSigma (rampedD P c') c') (rampedEps P c') hPh.1 hPh.2.1
    obtain ⟨C, -, hdec, -⟩ := hK7 P (rampedD P c') hd.1 hd1
    have ht0 : 0 < t := by linarith
    set x : ℝ := xOf c' t with hxdef
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hxt : c' * x ^ 2 / 3 = t := by
      rw [hxdef]; unfold xOf
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    have hpos' := hP x hx0 (by rw [hxt]; exact ht)
    have heq := rampedG_eq_twoG P hc' hI hdec hx0 (by rw [hxt]; exact ht0)
    rw [hxt] at heq
    unfold rampedG
    linarith

/-- `T_V(c') ≤ t_*(P, c') + 1` for `c'` large, for the parameters `P` of `rampedG_isFeasible_prob`. -/
theorem threshold_le_rampedTstar_prob (prob : FixedWeightProblem) (hw : prob.w = 1) :
    ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop, prob.T_V c' ≤ rampedTstar P c' + 1 := by
  obtain ⟨P, hP⟩ := rampedG_isFeasible_prob prob hw
  refine ⟨P, ?_⟩
  filter_upwards [hP] with c' ⟨hT, hfeas⟩
  exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, rampedG P c', hfeas⟩

/-- **The `O(1)` upper bound for every weight-one problem** (`rem:thmU`, Lemma `U*`): `T_V(c̃) ≤ T_*(c̃) + D_+`
for `c̃` large, with `D_+ = 1 + (A_opt/|a_1|) M_0 + C`.  This is `TheoremC15UpperInput prob` for every `prob`
with `prob.w = 1`. -/
theorem theoremC15UpperInput_prob (prob : FixedWeightProblem) (hw : prob.w = 1) :
    TheoremC15UpperInput prob := by
  obtain ⟨P, hTV⟩ := threshold_le_rampedTstar_prob prob hw
  obtain ⟨C, hC, hthr⟩ := rampedThreshold
  have ha1 : 0 < |airyZero 1| := abs_pos.2 (airyZero_neg 1).ne
  have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
  have hM : 0 ≤ Aopt / |airyZero 1| * P.M0 := by have := P.M0_pos; positivity
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 ((hTV.and (hthr P)).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max c₂ (max 1 (12 * prob.totalShift)), 1 + Aopt / |airyZero 1| * P.M0 + C,
    le_max_right _ _, by positivity, fun {c} hc => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc₂ c ((le_max_left _ _).trans hc)
  have hc0 : 0 < c := by linarith
  have hr : c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h3 (by norm_num)
  have h4 : C * c ^ (-(1 / 3 : ℝ)) ≤ C := by nlinarith
  have h5 := (abs_le.1 h2).2
  unfold TStar
  linarith

/-- Feasibility at the gap `t_* + 1` at Virasoro: `rampedG_isFeasible_prob` at `virasoroProblem`. -/
theorem rampedG_isFeasible : ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop,
    0 < rampedTstar P c' + 1 ∧
      virasoroProblem.IsFeasible (c' / 12) (rampedTstar P c' + 1) (rampedG P c') :=
  rampedG_isFeasible_prob virasoroProblem rfl

/-- `T_V(c') ≤ t_*(P, c') + 1` for `c'` large at Virasoro. -/
theorem threshold_le_rampedTstar : ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop,
    virasoroProblem.T_V c' ≤ rampedTstar P c' + 1 :=
  threshold_le_rampedTstar_prob virasoroProblem rfl

/-- **The `O(1)` upper bound at Virasoro** (`rem:thmU`, Lemma `U*`): `T_V(c̃) ≤ T_*(c̃) + D_+` for `c̃` large.
This is the input `TheoremC15UpperInput virasoroProblem` of Corollary E1. -/
theorem theoremC15UpperInput_virasoro : TheoremC15UpperInput virasoroProblem :=
  theoremC15UpperInput_prob virasoroProblem rfl

/-- **Virasoro, Corollary E1, unconditional**: the two-sided `O(1)` law
`Δ_best = c/Λ_V + A_opt c^{1/3} + O(1)`, `T_V = T_* + O(1)`, the extremal crossing measure and the `(Gap)`
clause `(T_V(c_j) - T_*(c_j))/c_j^{1/3} → 0`; `virasoro_corollary_E1` with `TheoremC15UpperInput` discharged. -/
theorem virasoro_corollary_E1_unconditional :
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
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :=
  virasoro_corollary_E1 theoremC15UpperInput_virasoro

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedG_isFeasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedG_isFeasible

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.threshold_le_rampedTstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threshold_le_rampedTstar

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.theoremC15UpperInput_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremC15UpperInput_virasoro

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.virasoro_corollary_E1_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_corollary_E1_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedG_isFeasible_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedG_isFeasible_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.threshold_le_rampedTstar_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threshold_le_rampedTstar_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.theoremC15UpperInput_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremC15UpperInput_prob

end FormalResearch.ModularBootstrap.Upper.Ramped
