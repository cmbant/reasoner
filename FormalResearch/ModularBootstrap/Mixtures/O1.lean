module

public import FormalResearch.ModularBootstrap.Mixtures.RampedUpper
public import FormalResearch.ModularBootstrap.Mixtures.O1Lower

/-!
# `pmix:o1` (Corollary PM.7): the two-sided bounded remainder for positive mixtures

`positive_mixtures.tex`, Corollary PM.7.  In the un-rebased variable `n = c̃`, `a = c̃/12`, for a positive mixture `M`
(`MixtureData`, the setting `(H_{w,mix})`) and `T_*(c̃) = ξ̄ c̃ + A_opt c̃^{1/3}`:

* `pmix_o1_feasible_mixture`, `pmix_o1_upper_mixture`: **upper half**: rebasing `n' = n - 12 r_min`
  (`MixtureData.rebase`, `pmix:rebase`), the rebased mixture is a `CommonSource` (`MixtureData.commonSource`), so
  `pmix_o1_feasible_common` (bumped ramped comb, `pmix_smooth`, `pmix:crossing` (b)) gives a strictly feasible test at the
  gap `T_*(n') + D_+ ≤ T_*(n) + D_+`, hence `T_mix(n) ≤ T_*(n) + D_+`;
* `pmix_o1_lower_mixture` (`O1Lower`): **lower half**: `T ≥ T_*(n) - D_-` for every weakly feasible test, by the component
  comparison and the weak single-component bound of Theorem `W1'(1)`;
* `pmix_o1_mixture`: `T_*(c) - D_- ≤ T_weak,mix(c) ≤ T_mix(c) ≤ T_*(c) + D_+` for `c ≥ c₁`;
  `pmix_o1_Delta`: `Δ_mix(c) = c/Λ_V + A_opt c^{1/3} + O(1)`;
* `pmix_o1_levels_mixture`: every mixed crossing measure has a level below `T_*(c) + D_+` (`pmix:crossing` (a));
* `pmix_o1_upper_common`, `pmix_o1_levels_common` (`RampedUpper`): the upper half and the levels for every common source
  (signed `λ` with the comparison floor);
* `theoremC15UpperInput_of_common`: the W-P6 bound `TheoremC15UpperInput prob` is the case `src = ofProblem prob` (floor
  `Q_0 = Q`, `d_λ = 1`).

Not covered: the lower half for a general signed common source (needs Theorem `W1'(1)` on `SourceUniformAxioms`, not re-run),
and the `liminf` bound (`pmix:liminf`) with `c_0^*` (needs `ctu:c0` and `int:strict-weak`).  All results are proved
unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight

lemma TStar_mono {c c' : ℝ} (hc' : 0 ≤ c') (h : c' ≤ c) : TStar c' ≤ TStar c := by
  have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
  have hxb : 0 ≤ xiBar := by unfold xiBar; positivity
  unfold TStar
  have := Real.rpow_le_rpow hc' h (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
  nlinarith only [mul_le_mul_of_nonneg_left h hxb, mul_le_mul_of_nonneg_left this hA]

namespace MixtureData

variable (M : MixtureData)

/-- **`pmix:o1`, upper half, feasible form, positive mixtures (un-rebased)**: for `c̃ ≥ c₂` the mixture has a strictly
feasible test function at the gap `T_*(c̃) + D_+`. -/
theorem pmix_o1_feasible_mixture :
    ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ {c : ℝ}, c₂ ≤ c →
      0 < TStar c + D ∧ ∃ g : ℝ → ℝ, M.toSource.IsFeasible (c / 12) (TStar c + D) g := by
  obtain ⟨i₀, hi₀⟩ := M.rebase_exists_zero
  obtain ⟨c₂, D, -, hD, h⟩ := pmix_o1_feasible_common (M.rebase.commonSource hi₀)
  refine ⟨max c₂ 1 + 12 * M.rmin, D, hD, fun {c} hc => ?_⟩
  have hrm := M.rmin_nonneg
  have hc' : max c₂ 1 ≤ c - 12 * M.rmin := by linarith
  have hc2 : c₂ ≤ c - 12 * M.rmin := (le_max_left _ _).trans hc'
  have hc1 : 1 ≤ c - 12 * M.rmin := (le_max_right _ _).trans hc'
  obtain ⟨hpos, g, hg⟩ := h hc2
  have hmono : TStar (c - 12 * M.rmin) ≤ TStar c := TStar_mono (by linarith) (by linarith)
  have hD1 : (c - 12 * M.rmin) / 12 = c / 12 - M.rmin := M.rebase_charge c
  rw [hD1] at hg
  have hg' : M.toSource.IsFeasible (c / 12) (TStar (c - 12 * M.rmin) + D) g :=
    (M.rebase_isFeasible_iff).1 hg
  exact ⟨by linarith, g, hg'.1, hg'.2.1, fun t ht => hg'.2.2 t (by linarith)⟩

/-- **`pmix:o1`, upper half, positive mixtures (un-rebased)**: `T_mix(c̃) ≤ T_*(c̃) + D_+` for `c̃ ≥ c₂`. -/
theorem pmix_o1_upper_mixture :
    ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ {c : ℝ}, c₂ ≤ c → M.toSource.T_V c ≤ TStar c + D := by
  obtain ⟨c₂, D, hD, h⟩ := M.pmix_o1_feasible_mixture
  refine ⟨c₂, D, hD, fun {c} hc => ?_⟩
  obtain ⟨hT, g, hg⟩ := h hc
  exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, g, hg⟩

/-- **`pmix:o1`, two-sided bounded remainder for positive mixtures**: there are `c₁`, `D_-, D_+ ≥ 0` (depending only on the
fixed mixture data) with `T_*(c) - D_- ≤ T_weak,mix(c) ≤ T_mix(c) ≤ T_*(c) + D_+` for all `c ≥ c₁`, where
`T_*(c) = ξ̄ c + A_opt c^{1/3}`. -/
theorem pmix_o1_mixture :
    ∃ c₁ D_m D_p : ℝ, 0 ≤ D_m ∧ 0 ≤ D_p ∧ ∀ {c : ℝ}, c₁ ≤ c →
      TStar c - D_m ≤ M.toSource.T_weak c ∧ M.toSource.T_weak c ≤ M.toSource.T_V c ∧
        M.toSource.T_V c ≤ TStar c + D_p := by
  obtain ⟨c₂, D_p, hDp, hfe⟩ := M.pmix_o1_feasible_mixture
  obtain ⟨c₃, D_m, hDm, -, hlow⟩ := pmix_o1_lower_mixture M
  refine ⟨max c₂ c₃, D_m, D_p, hDm, hDp, fun {c} hc => ?_⟩
  obtain ⟨hT, g, hg⟩ := hfe ((le_max_left _ _).trans hc)
  have hg0 : ∃ t ≥ (0 : ℝ), g t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : M.toSource.gVac (c / 12) g = 0 := by
      unfold ShiftSource.gVac
      have : ∫ t in Ioi (0 : ℝ), g t * M.toSource.cardyV (c / 12) t = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
        rw [hcon t (mem_Ioi.mp ht).le, zero_mul]
      rw [this]; ring
    linarith [hg.2.1]
  have hweak : M.toSource.IsWeaklyFeasible (c / 12) (TStar c + D_p) g :=
    ⟨hg.1, hg0, hg.2.1.le, hg.2.2⟩
  have hne_w : {T : ℝ | 0 < T ∧ ∃ g, M.toSource.IsWeaklyFeasible (c / 12) T g}.Nonempty :=
    ⟨_, hT, g, hweak⟩
  have hbdd : BddBelow {T : ℝ | 0 < T ∧ ∃ g, M.toSource.IsWeaklyFeasible (c / 12) T g} :=
    ⟨0, fun T hT => hT.1.le⟩
  have hc3 : c₃ ≤ c := (le_max_right _ _).trans hc
  have hlo : TStar c - D_m ≤ M.toSource.T_weak c := by
    refine le_csInf hne_w ?_
    rintro T ⟨-, g', hg'⟩
    exact hlow hc3 hg'
  have hne_s : {T : ℝ | 0 < T ∧ ∃ g, M.toSource.IsFeasible (c / 12) T g}.Nonempty := ⟨_, hT, g, hg⟩
  have hweak_le : M.toSource.T_weak c ≤ M.toSource.T_V c := by
    refine csInf_le_csInf hbdd hne_s ?_
    rintro T ⟨hT0, g', hg'⟩
    refine ⟨hT0, g', hg'.1, ?_, hg'.2.1.le, hg'.2.2⟩
    by_contra hcon
    push Not at hcon
    have : M.toSource.gVac (c / 12) g' = 0 := by
      unfold ShiftSource.gVac
      have : ∫ t in Ioi (0 : ℝ), g' t * M.toSource.cardyV (c / 12) t = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
        rw [hcon t (mem_Ioi.mp ht).le, zero_mul]
      rw [this]; ring
    linarith [hg'.2.1]
  have hup : M.toSource.T_V c ≤ TStar c + D_p :=
    csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, g, hg⟩
  exact ⟨hlo, hweak_le, hup⟩

/-- **`pmix:o1`, the gap**: `Δ_mix(c) = c/Λ_V + A_opt c^{1/3} + O(1)`, with `Δ_mix(c) = c/12 + T_mix(c)`. -/
theorem pmix_o1_Delta :
    ∃ c₁ D : ℝ, 0 ≤ D ∧ ∀ {c : ℝ}, c₁ ≤ c →
      |M.toSource.Delta_best c - (c / lambdaV + Aopt * c ^ ((1 : ℝ) / 3))| ≤ D := by
  obtain ⟨c₁, D_m, D_p, hDm, hDp, h⟩ := M.pmix_o1_mixture
  refine ⟨c₁, max D_m D_p, le_max_of_le_left hDm, fun {c} hc => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h hc
  have e := TStar_add_div_twelve c
  unfold ShiftSource.Delta_best
  rw [abs_le]
  constructor <;> nlinarith only [h1, h2, h3, e, le_max_left D_m D_p, le_max_right D_m D_p]

/-- Transport of a mixed crossing measure to the rebased mixture (same Cardy density). -/
noncomputable def crossingRebase {a : ℝ} (m : SourceCrossingMeasure M.toSource a) :
    SourceCrossingMeasure M.rebase.toSource (a - M.rmin) where
  ν := m.ν
  supp_nonneg := m.supp_nonneg
  finite_laplace := m.finite_laplace
  crossing {β} hβ := by
    have h := m.crossing hβ
    simp only [ShiftSource.cardyDensity] at h ⊢
    simp only [rebase_toSource_w, M.rebase_cardyV]
    exact h

/-- **`pmix:o1`: every admissible spectrum has a level below `T_* + D_+`** for a positive mixture (un-rebased):
every mixed crossing measure `ν` at `a = c̃/12`, `c̃ ≥ c₂`, charges `[0, T_*(c̃) + D_+)`. -/
theorem pmix_o1_levels_mixture :
    ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ {c : ℝ}, c₂ ≤ c → ∀ meas : SourceCrossingMeasure M.toSource (c / 12),
      ¬ meas.ν (Iio (TStar c + D)) = 0 := by
  obtain ⟨i₀, hi₀⟩ := M.rebase_exists_zero
  obtain ⟨c₂, D, h12, hD, h⟩ := pmix_o1_feasible_common (M.rebase.commonSource hi₀)
  refine ⟨max c₂ 1 + 12 * M.rmin, D, hD, fun {c} hc meas => ?_⟩
  have hrm := M.rmin_nonneg
  have hc' : max c₂ 1 ≤ c - 12 * M.rmin := by linarith
  have hc2 : c₂ ≤ c - 12 * M.rmin := (le_max_left _ _).trans hc'
  have hc1 : 1 ≤ c - 12 * M.rmin := (le_max_right _ _).trans hc'
  obtain ⟨-, g, hg⟩ := h hc2
  have hmono : TStar (c - 12 * M.rmin) ≤ TStar c := TStar_mono (by linarith) (by linarith)
  have hD1 : (c - 12 * M.rmin) / 12 = c / 12 - M.rmin := M.rebase_charge c
  rw [hD1] at hg
  have hAt : (M.rebase.commonSource hi₀).F.At (c / 12 - M.rmin) :=
    (M.rebase.commonSource hi₀).at_ (by
      have : 12 * (M.rebase.commonSource hi₀).a₀ ≤ c₂ := h12
      linarith)
  have hge : ∀ t : ℝ, TStar c + D ≤ t → 0 ≤ g t := fun t ht => hg.2.2 t (by linarith)
  exact pmix_crossing_a_exclusion hAt (M.crossingRebase meas) hg.1 hge hg.2.1

end MixtureData

/-- **The W-P6 upper bound is the single-component case**: `TheoremC15UpperInput prob`
(`T_V(c̃) ≤ T_*(c̃) + D_+`, `Upper.Ramped.theoremC15UpperInput_probW`) follows from `pmix_o1_upper_common` for the source
`ShiftSource.ofProblem prob`, with floor data `Q_0 = Q`, `d_λ = 1`. -/
theorem theoremC15UpperInput_of_common (prob : FixedWeightProblem) : TheoremC15UpperInput prob := by
  have hshift : ∀ {a : ℝ}, max prob.totalShift 1 ≤ a → (ShiftSource.ofProblem prob).ShiftLE a := fun {a} ha =>
    (ofProblem_shiftLE_iff prob).2 ((le_max_left _ _).trans ha)
  let F : FloorData (ShiftSource.ofProblem prob) := ⟨prob.m, prob.μ, prob.hμ, 1, one_pos⟩
  let C : CommonSource :=
    { src := ShiftSource.ofProblem prob
      F := F
      a₀ := max prob.totalShift 1
      at_ := fun {a} ha =>
        { pos := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ha)
          shift := hshift ha
          prob_shift := (le_max_left _ _).trans ha
          floor := fun t _ => by
            rw [one_mul]
            exact le_refl _ } }
  obtain ⟨c₂, D, hD, h⟩ := pmix_o1_upper_common C
  refine ⟨max c₂ (max 1 (12 * prob.totalShift)), D, le_max_right _ _, hD, fun {c} hc => ?_⟩
  have := h ((le_max_left _ _).trans hc)
  rwa [show C.src.T_V c = prob.T_V c from ofProblem_T_V prob c] at this

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_o1_feasible_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_o1_feasible_mixture

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_o1_upper_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_o1_upper_mixture

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_o1_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_o1_mixture

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_o1_Delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_o1_Delta

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_o1_levels_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixtureData.pmix_o1_levels_mixture

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.theoremC15UpperInput_of_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremC15UpperInput_of_common

end FormalResearch.ModularBootstrap.Mixtures
