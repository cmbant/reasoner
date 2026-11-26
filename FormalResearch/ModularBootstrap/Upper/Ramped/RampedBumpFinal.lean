module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpVacuum
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedThreshold
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# Lemma `U*(w)` assembled: the `O(1)` upper bound `T_V(c̃) ≤ T_*(c̃) + D_+` for every fixed-weight problem (`fw:Ustar`)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`; at one component `pmix:ramped`), with
`upper_transfer.tex` (`ut:Phi`, `ut:III`, `ut:V`) and the bump of `fw:s1`.

* `rampedBumpG prob P c'`: the test function `g_w = ½(h₀^{(p)} - 𝓗_w h₀^{(p)})` of the bumped ramped design
  `R_bump · D_*` at `d = rampedD P c'` (`pairOdd` of the bumped comb profile and its order-`(w-1)` Hankel transform),
  with the bump `(rpParams (w - 1)).bumpData` and the cut `rampedBumpCut`;
* `rampedBumpG_isFeasible_prob`: there is `P` such that eventually in `c'` `rampedBumpG prob P c'` is feasible for
  `prob` at `a = c'/12` and gap `T = t_*(P, c') + 1`: membership (`rampedBumped_k7`), `g_w ≥ 0` for
  `t ≥ t_* + 1` (`rampedBumped_positive`, `twoGW = 2 g_w` by `InnerCombHyp.edgeHankelP_eq`) and `g_vac > 0`
  (`rampedBumpVacuum`);
* `threshold_le_rampedTstar_probW`: `T_V(c') ≤ t_*(P, c') + 1` for `c'` large;
* **`theoremC15UpperInput_probW`**: `T_V(c̃) ≤ T_*(c̃) + D_+` for `c̃` large, for every `prob : FixedWeightProblem`,
  that is `TheoremC15UpperInput prob`, the hypothesis `H3` of `FoldTip.ft_fixedWeight_modH3` at every weight.

Order of constants: bump data (`r_p`, `X_p`, `η_big`, depending on `w` only) → `C_I` → `C_mid ≥ max(C_sep, ...)` → `M_0` → `c_0`.

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
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.Special

/-- The bumped ramped comb of `prob` at `(P, c')`, `d = rampedD P c'`, with the bump of `rpParams (w - 1)` and the cut
`rampedBumpCut`. -/
noncomputable def rampedBumpComb (prob : FixedWeightProblem) (P : RampedParams) (c' : ℝ) : ℂ → ℂ :=
  designComb c' 1 (rampedBumpCut (rpParams (prob.w - 1)).bumpData P c') (1 / 4)
    (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
    (bumpEps (rpParams (prob.w - 1)).bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))

/-- The test function `g_w = ½(h₀^{(p)} - 𝓗_w h₀^{(p)})` of the bumped ramped design `R_bump · D_*` at `d = M_0 c'^{-1/3}`. -/
noncomputable def rampedBumpG (prob : FixedWeightProblem) (P : RampedParams) (c' : ℝ) : ℝ → ℝ :=
  pairOdd (combProfile c' (rampedBumpComb prob P c'))
    (hankelTransform prob.w (combProfile c' (rampedBumpComb prob P c')))

/-- **Feasibility of the bumped ramped design at the gap `t_* + 1`, every fixed-weight problem** (`fw:Ustar`): there is
`P` such that for `c'` large `g_w` of the bumped ramped comb is feasible for `prob` at `a = c'/12` and `T = t_*(P, c') + 1`. -/
theorem rampedBumpG_isFeasible_prob (prob : FixedWeightProblem) :
    ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop,
      0 < rampedTstar P c' + 1 ∧ prob.IsFeasible (c' / 12) (rampedTstar P c' + 1) (rampedBumpG prob P c') := by
  set Pp := rpParams (prob.w - 1) with hPp
  obtain ⟨CI, C₀, hCI, hC₀, hpos⟩ := rampedBumped_positive (prob.w - 1) Pp
  obtain ⟨M0, hM0, hvac⟩ := rampedBumpVacuum prob Pp.bumpData CI C₀ hCI hC₀
  obtain ⟨P, hP1, hP2, hP3⟩ : ∃ P : RampedParams, P.CI = CI ∧ P.Cmid = C₀ ∧ P.M0 = M0 :=
    ⟨⟨CI, C₀, M0, hCI, hC₀, hM0⟩, rfl, rfl, rfl⟩
  refine ⟨P, ?_⟩
  filter_upwards [hpos P hP1 hP2.ge, hvac P hP1 hP2 hP3 (rampedBumpCut Pp.bumpData P)
      (le_rampedBumpCut Pp.bumpData P), rampedBumped_k7 prob Pp.bumpData, ramped_phaseHyp,
    bumped_phaseHyp Pp.bumpData 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    rampedD_mem P, eventually_gt_atTop (0 : ℝ)]
    with c' hP hV hK7 hph hbph hin hd hc'
  have hd1 : rampedD P c' ≤ 1 := hd.2.trans rampedD0_le_one
  have hT0 : 0 < rampedTstar P c' + 1 := by
    have : 0 ≤ rampedTstar P c' := by unfold rampedTstar; positivity
    linarith
  have hN := le_rampedBumpCut Pp.bumpData P c'
  obtain ⟨C, hC0, hd1', hd2', hT, -⟩ := hK7 P (rampedD P c') hd.1 hd1 _ hN
  refine ⟨hT0, hT, hV, fun t ht => ?_⟩
  have hph' := hbph (nCap P c' + 6) (rampedBumpCut Pp.bumpData P c') (rampedSigma (rampedD P c') c')
    (rampedEps P c') 1 (hph P (rampedD P c') hd.1 hd1) hN
  have hI : InnerCombHyp c' (rampedBumpComb prob P c') := hin _ _ _ hph'.1 hph'.2.1
  have ht0 : 0 < t := by linarith
  have hx0 : 0 ≤ xOf c' t := xOf_nonneg c' t
  have hxt : c' * xOf c' t ^ 2 / 3 = t := by
    unfold xOf
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hpos' := hP (xOf c' t) hx0 (by rw [hxt]; exact ht)
  have hh : designProfile c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
      (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
      (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) ((xOf c' t : ℝ) : ℂ) =
      ((combProfile c' (rampedBumpComb prob P c') t : ℝ) : ℂ) := by
    have := hI.combProfile_eq (s := t) ht0
    rw [← combH0_designComb]
    exact this
  have e2 := hI.edgeHankelP_eq (prob.w - 1) hc' hd1' ht0
  rw [Nat.sub_add_cancel prob.hw] at e2
  unfold twoGW at hpos'
  rw [hxt, hh] at hpos'
  have e3 : edgeHankelP (prob.w - 1) c' (designProfile c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
      (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
      (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t =
      ((hankelTransform prob.w (combProfile c' (rampedBumpComb prob P c')) t : ℝ) : ℂ) := by
    rw [← combH0_designComb]
    exact e2
  rw [e3] at hpos'
  simp only [Complex.sub_re, Complex.ofReal_re] at hpos'
  unfold rampedBumpG pairOdd
  linarith

/-- `T_V(c') ≤ t_*(P, c') + 1` for `c'` large, for the parameters `P` of `rampedBumpG_isFeasible_prob`. -/
theorem threshold_le_rampedTstar_probW (prob : FixedWeightProblem) :
    ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop, prob.T_V c' ≤ rampedTstar P c' + 1 := by
  obtain ⟨P, hP⟩ := rampedBumpG_isFeasible_prob prob
  refine ⟨P, ?_⟩
  filter_upwards [hP] with c' ⟨hT, hfeas⟩
  exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, rampedBumpG prob P c', hfeas⟩

/-- **The `O(1)` upper bound for every fixed-weight problem** (`fw:Ustar`, Lemma `U*(w)`): `T_V(c̃) ≤ T_*(c̃) + D_+`
for `c̃` large, with `D_+ = 1 + (A_opt/|a_1|) M_0 + C`.  This is `TheoremC15UpperInput prob`, for every `prob`. -/
theorem theoremC15UpperInput_probW (prob : FixedWeightProblem) : TheoremC15UpperInput prob := by
  obtain ⟨P, hTV⟩ := threshold_le_rampedTstar_probW prob
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

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBumpG_isFeasible_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumpG_isFeasible_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.threshold_le_rampedTstar_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threshold_le_rampedTstar_probW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.theoremC15UpperInput_probW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremC15UpperInput_probW

end FormalResearch.ModularBootstrap.Upper.Ramped
