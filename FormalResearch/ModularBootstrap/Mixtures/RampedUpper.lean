module

public import FormalResearch.ModularBootstrap.Mixtures.RampedSource
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpFinal

/-!
# `pmix:o1`, upper half: the `+O(1)` upper bound for a common source

`positive_mixtures.tex`, Lemma PM.7 (`pmix:o1`), "Upper bound" paragraph.  For a `CommonSource` `C` (an atomic signed shift
measure with the comparison floor `V ≥ d_λ V_{w,Q_0}` at all large charge; positive mixtures after rebasing are instances,
`MixtureData.commonSource`) the bumped ramped comb of weight `w = C.src.w` (`pmix:ramped`) with the smooth-multiplier
vacuum transfer (`pmix_smooth`) and `pmix:crossing` (b) (`k7_src`) gives a feasible test function for the source:

* `rampedBumpG_isFeasible_src`: there is `P` with, for all large `c'`, `g_w = rampedBumpG (Q ≡ 1) P c'` strictly feasible for
  the source `C.src` at `a = c'/12` and gap `t_*(P, c') + 1`: `g_w ∈ \overline{\mathcal A}_{w,src}` (`k7_src`),
  `g_w ≥ 0` for `t ≥ t_* + 1` (`pmix:ramped`, source free) and `g_vac ≥ π √c' - C_vac > 0`
  (`pmix_smooth`, `C_vac = ‖λ‖_TV`);
* `pmix_o1_feasible_common`: for `c̃ ≥ c₂` a strictly feasible test function at the gap `T_*(c̃) + D_+`;
* **`pmix_o1_upper_common`**: `T_V(c̃) ≤ T_*(c̃) + D_+` for all `c̃ ≥ c₂`, for every `CommonSource`;
* `pmix_o1_levels_common`: every mixed crossing measure has a level below `T_*(c̃) + D_+` (`pmix:crossing` (a)).

The comb `rampedBumpG` depends on the problem only through its weight, so it is taken from the trivial product `Q ≡ 1` of weight
`w` (`FixedWeight.trivialProductProblem`); the source enters through `pmix_smooth` (its weight family `V c' = src.cardyV (c'/12)`)
and `k7_src`.  All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Ramped FormalResearch.Special

/-- **Feasibility of the bumped ramped design for a common source** (`pmix:o1`, upper bound): see the module docstring. -/
theorem rampedBumpG_isFeasible_src (C : CommonSource) :
    ∃ P : RampedParams, ∀ᶠ c' : ℝ in atTop,
      0 < rampedTstar P c' + 1 ∧
        C.src.IsFeasible (c' / 12) (rampedTstar P c' + 1)
          (rampedBumpG (trivialProductProblem C.src.w C.src.hw) P c') := by
  set triv := trivialProductProblem C.src.w C.src.hw with htriv
  obtain ⟨W, hWV, -⟩ := exists_smoothWeight C
  set Pp := rpParams (triv.w - 1) with hPp
  obtain ⟨CI, C₀, hCI, hC₀, hpos⟩ := rampedBumped_positive (triv.w - 1) Pp
  obtain ⟨M0, hM0, hvac⟩ := pmix_smooth W Pp.bumpData CI C₀ hCI hC₀
  obtain ⟨P, hP1, hP2, hP3⟩ : ∃ P : RampedParams, P.CI = CI ∧ P.Cmid = C₀ ∧ P.M0 = M0 :=
    ⟨⟨CI, C₀, M0, hCI, hC₀, hM0⟩, rfl, rfl, rfl⟩
  refine ⟨P, ?_⟩
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  have hπ := Real.pi_pos
  filter_upwards [hpos P hP1 hP2.ge, hvac P hP1 hP2 hP3 (rampedBumpCut Pp.bumpData P)
      (le_rampedBumpCut Pp.bumpData P), rampedBumped_k7 triv Pp.bumpData, ramped_phaseHyp,
    bumped_phaseHyp Pp.bumpData 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    rampedD_mem P, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * C.a₀),
    eventually_ge_atTop ((C.src.tv / π + 1) ^ 2)]
    with c' hP hV hK7 hph hbph hin hd hc' hcA hbig
  have hAt : C.F.At (c' / 12) := C.at_ (by linarith)
  have hd1 : rampedD P c' ≤ 1 := hd.2.trans rampedD0_le_one
  have hT0 : 0 < rampedTstar P c' + 1 := by
    have : 0 ≤ rampedTstar P c' := by unfold rampedTstar; positivity
    linarith
  have hN := le_rampedBumpCut Pp.bumpData P c'
  have hK := hK7 P (rampedD P c') hd.1 hd1 _ hN
  have hph' := hbph (nCap P c' + 6) (rampedBumpCut Pp.bumpData P c') (rampedSigma (rampedD P c') c')
    (rampedEps P c') 1 (hph P (rampedD P c') hd.1 hd1) hN
  have hI : InnerCombHyp c' (rampedBumpComb triv P c') := hin _ _ _ hph'.1 hph'.2.1
  obtain ⟨hTest, hid, hn⟩ := k7_src hc' hAt hI hK
  obtain ⟨Cd, hCd0, hdec, hdec', -, -, -⟩ := hK
  -- the vacuum pairing
  have hIw : (∫ t in Ioi 0, combProfile c' (rampedBumpComb triv P c') t * C.src.cardyV (c' / 12) t) ≤
      -√c' := by
    have e : ∀ t, rampedBumpFS W Pp.bumpData P (rampedD P c') c' (rampedBumpCut Pp.bumpData P c') t =
        combProfile c' (rampedBumpComb triv P c') t * C.src.cardyV (c' / 12) t := fun t => by
      unfold rampedBumpFS
      rw [hWV]
      rfl
    simp_rw [e] at hV
    exact hV
  have hgv : 0 < C.src.gVac (c' / 12)
      (pairOdd (combProfile c' (rampedBumpComb triv P c'))
        (hankelTransform C.src.w (combProfile c' (rampedBumpComb triv P c')))) := by
    have hre := congrArg Complex.re hid
    rw [← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    have hhalf := (Complex.abs_re_le_norm _).trans hn
    have hgv' := abs_le.mp hhalf
    have hsc : C.src.tv / π + 1 ≤ √c' := by
      calc C.src.tv / π + 1 = √((C.src.tv / π + 1) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ √c' := Real.sqrt_le_sqrt hbig
    have hgoal : C.src.tv < π * √c' := by
      have h1 : C.src.tv / π < √c' := by linarith
      rwa [div_lt_iff₀ hπ, mul_comm] at h1
    rw [hre]
    have hpi := mul_le_mul_of_nonneg_left hIw hπ.le
    linarith only [hpi, hgv'.1, hgoal]
  refine ⟨hT0, hTest, hgv, fun t ht => ?_⟩
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
      ((combProfile c' (rampedBumpComb triv P c') t : ℝ) : ℂ) := by
    have := hI.combProfile_eq (s := t) ht0
    rw [← combH0_designComb]
    exact this
  have e2 := hI.edgeHankelP_eq (triv.w - 1) hc' hdec ht0
  rw [Nat.sub_add_cancel triv.hw] at e2
  unfold twoGW at hpos'
  rw [hxt, hh] at hpos'
  have e3 : edgeHankelP (triv.w - 1) c' (designProfile c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
      (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
      (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t =
      ((hankelTransform triv.w (combProfile c' (rampedBumpComb triv P c')) t : ℝ) : ℂ) := by
    rw [← combH0_designComb]
    exact e2
  rw [e3] at hpos'
  simp only [Complex.sub_re, Complex.ofReal_re] at hpos'
  unfold rampedBumpG pairOdd
  linarith

/-- **`pmix:o1`, upper half, feasible form**: for every `CommonSource` there are `c₂ ≥ 12 a₀` and `D_+ ≥ 0` such that for
all `c̃ ≥ c₂` the source has a strictly feasible test function at the gap `T_*(c̃) + D_+`
(`T_*(c̃) = ξ̄ c̃ + A_opt c̃^{1/3}`): `g ∈ \overline{\mathcal A}_{w,src}`, `g ≥ 0` on `[T_* + D_+, ∞)`, `g_vac > 0`. -/
theorem pmix_o1_feasible_common (C : CommonSource) :
    ∃ c₂ D : ℝ, 12 * C.a₀ ≤ c₂ ∧ 0 ≤ D ∧ ∀ {c : ℝ}, c₂ ≤ c →
      0 < TStar c + D ∧ ∃ g : ℝ → ℝ, C.src.IsFeasible (c / 12) (TStar c + D) g := by
  obtain ⟨P, hF⟩ := rampedBumpG_isFeasible_src C
  obtain ⟨Ct, hCt, hthr⟩ := rampedThreshold
  have ha1 : 0 < |airyZero 1| := abs_pos.2 (airyZero_neg 1).ne
  have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
  have hM : 0 ≤ Aopt / |airyZero 1| * P.M0 := by have := P.M0_pos; positivity
  have ha₀ : 0 < C.a₀ := (C.at_ (le_refl C.a₀)).pos
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 ((hF.and (hthr P)).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max c₂ (12 * C.a₀), 1 + Aopt / |airyZero 1| * P.M0 + Ct, le_max_right _ _, by positivity,
    fun {c} hc => ?_⟩
  obtain ⟨⟨⟨hT0, hfeas⟩, h2⟩, h3⟩ := hc₂ c ((le_max_left _ _).trans hc)
  have hc0 : 0 < c := by linarith
  have hr : c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h3 (by norm_num)
  have h4 : Ct * c ^ (-(1 / 3 : ℝ)) ≤ Ct := by nlinarith
  have h5 := (abs_le.1 h2).2
  have hTS : 0 ≤ TStar c := by
    unfold TStar
    have hxb : 0 ≤ xiBar := by unfold xiBar; positivity
    have := Real.rpow_nonneg hc0.le ((1 : ℝ) / 3)
    positivity
  have hle : rampedTstar P c + 1 ≤ TStar c + (1 + Aopt / |airyZero 1| * P.M0 + Ct) := by
    unfold TStar at h5 ⊢
    linarith
  refine ⟨by linarith, _, hfeas.1, hfeas.2.1, fun t ht => hfeas.2.2 t (by linarith)⟩

/-- **`pmix:o1`, upper half, for the common source class**: for every `CommonSource` there are `c₂` and `D_+ ≥ 0` with
`T_V(c̃) ≤ T_*(c̃) + D_+` for all `c̃ ≥ c₂`, where `T_*(c̃) = ξ̄ c̃ + A_opt c̃^{1/3}` and `T_V` is the strict threshold of the
source (`T_mix` for a rebased mixture, `MixtureData.commonSource`). -/
theorem pmix_o1_upper_common (C : CommonSource) :
    ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ {c : ℝ}, c₂ ≤ c → C.src.T_V c ≤ TStar c + D := by
  obtain ⟨c₂, D, -, hD, h⟩ := pmix_o1_feasible_common C
  refine ⟨c₂, D, hD, fun {c} hc => ?_⟩
  obtain ⟨hT, g, hg⟩ := h hc
  exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, g, hg⟩

/-- **`pmix:o1`: every admissible spectrum has a level below `T_* + D_+`** (upper half, via `pmix:crossing` (a)): for every
`CommonSource` there are `c₂` and `D_+` such that for `c̃ ≥ c₂` every mixed crossing measure `ν` at `a = c̃/12` (a positive
measure on `[0, ∞)` with finite Laplace transforms obeying the crossing equation) charges `[0, T_*(c̃) + D_+)`. -/
theorem pmix_o1_levels_common (C : CommonSource) :
    ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ {c : ℝ}, c₂ ≤ c → ∀ meas : SourceCrossingMeasure C.src (c / 12),
      ¬ meas.ν (Iio (TStar c + D)) = 0 := by
  obtain ⟨c₂, D, h12, hD, h⟩ := pmix_o1_feasible_common C
  refine ⟨c₂, D, hD, fun {c} hc meas => ?_⟩
  obtain ⟨-, g, hg⟩ := h hc
  have hAt : C.F.At (c / 12) := C.at_ (by linarith)
  exact pmix_crossing_a_exclusion hAt meas hg.1 hg.2.2 hg.2.1

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rampedBumpG_isFeasible_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumpG_isFeasible_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_feasible_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_feasible_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_levels_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_levels_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_upper_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_upper_common

end FormalResearch.ModularBootstrap.Mixtures
