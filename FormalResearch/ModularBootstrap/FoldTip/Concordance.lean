module

public import FormalResearch.ModularBootstrap.FixedWeightTip.BlowupAndRigidity
public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWInterface
public import FormalResearch.ModularBootstrap.FixedWeightBand.N1Lower
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFinal
public import FormalResearch.ModularBootstrap.Upper.Assembly.FarFirstSite
public import FormalResearch.ModularBootstrap.Upper.Assembly.N1

/-!
# Fold-tip concordance for Paper II's instances (`FT-0`)

Bundle theorems for the fold-tip conclusions of `CFT/modular_bootstrap/paper/fold_tip_universality.tex`,
Theorem FT (`ft:FT`), for a fixed-weight problem `prob : FixedWeightProblem`, and specialised to
`virasoroProblem` and `n1SuperVirasoroProblem`. No new mathematics: every component is an existing
declaration, reused in its existing statement form.

## Conclusion map

| FT conclusion | Lean component | supplied by |
|---|---|---|
| (C1) slope `T ≥ ξ̄c̃ − Cc̃^{1/3}` | `FixedWeight.FixedWeightLowerBoundInput prob` (`FTLower`) | `FixedWeightBand.fixedWeightLowerBoundInput_of_problem` (Theorem `W1'(1)`, `lower_o1_two_edge.tex`) |
| (C3) lower remainder, O(1) form `T ≥ T_* − D` | same | same (stronger than the TeX `−C log c̃`; the TeX form follows since `A_opt c̃^{1/3} ≥ 0`) |
| (C2) `liminf (T_c − ξ̄c̃) c̃^{-1/3} ≥ A` | `FTLiminf prob` | `FixedWeightTip.concrete_blowup_theorem_C_general` (Theorem C, with `Aopt = A`) |
| (C2) full, `T_c = ξ̄c̃ + A c̃^{1/3} + o(c̃^{1/3})` under (H3) | `FTAiryLaw prob`, clause `\|T_V − T_*\| ≤ C` | `FixedWeight.corollary_E1` with hypothesis `TheoremC15UpperInput prob` (H3) |
| (C4) `T_c ≤ ξ̄c̃ + A c̃^{1/3} + R⁺`, `R⁺ = O(1)` | `TheoremC15UpperInput prob` (upper clause of `FTAiryLaw`) | hypothesis (H3) for general `prob`; discharged for `prob.w = 1` by `Upper.Ramped.theoremC15UpperInput_prob` (Lemma `U*`, `rem:thmU`) |
| (C5a) profile `Ψ̃^h → f_*/(2L_*)` | `FTRigidity prob`, clauses R1 and R2 (`Φ → φ*` locally uniformly, `L¹` convergence, `s₁ → s₁*`) | `FixedWeightTip.concrete_blowup_theorem_R1_general`, `concrete_blowup_theorem_R2_general`, under `Att` from `att_of_upper_threshold_general` |
| (C5b) zeros of `g_c` converge to the nodes | `FTRigidity prob`, clause R3 | `FixedWeightTip.concrete_blowup_theorem_R3_general` under `Att` |
| (C5c) extremal measures `→ Σ_n Ai'(a_n)^{-2} δ_{a_n}`, **Airy level (`N = Ai`, `m = 1`) at weight one only**; the paper's C5(c) at every Hermite–Biehler level (via Lemmas WP, WR and the realigned H4b; package FT-H4b of `ModularBootstrap/PLAN.md`) is the target and is not in Lean | `FTSigma prob` (needs `prob.w = 1`) | `Upper.Assembly.sigma_unconditional_prob` (`FarFirstSite.lean`), with `FixedWeightLowerBoundInput` from `fixedWeightLowerBoundInput_of_problem` |
| (C5d) fixed prescribed levels, log rate | not bundled (FT-3..6 deferred) | none |

Hypotheses of Theorem FT, as realised by the Lean instances:

| TeX hypothesis | Lean declaration |
|---|---|
| (H1) band positivity, vacuum sign `∫Ψ_g ≤ η_vac` | built into `FixedWeightProblem.IsWeaklyFeasible` (`Crossing/Setup.lean`: `0 ≤ gVac`, `g ≥ 0` on `[T,∞)`); `η_vac ≡ 0` |
| (H2) holomorphic Airy envelope around the fold | `FixedWeightTip.psiTilde_analyticOnNhd prob` (H2-hol) and the envelope bound of `FixedWeightTip.proposition_P_of_problem` (`FixedWeightTip/PropositionP.lean`) |
| (H2+) rates `ς_c = O(c̃^{-1/3} log c̃)` | the envelope clause of `FixedWeightTip.proposition_P_of_problem` (Proposition P, `ft:PP`); used only by C3-log and C5d, which are not bundled |
| (H3) attainment `T_c ≤ ξ̄c̃ + A c̃^{1/3} + R⁺` | `FixedWeight.TheoremC15UpperInput prob`, discharged for `prob.w = 1` by `Upper.Ramped.theoremC15UpperInput_prob` (`RampedFinal.lean`); `virasoro`: `theoremC15UpperInput_virasoro`; `N = 1`: `n1_theoremC15UpperInput` |
| (H4a) holomorphic, zero-free `W_c` on compacts | `FixedWeightTip.propP_H4a_eventually_ne_zero` (zero-freeness on the Langer disc, from `UniformPropositionPData`), with holomorphy from `psiTilde_analyticOnNhd` |
| (H4b) crossing measures pair with comb tests (Property `sr:P`) | `Upper.Assembly.displacedPropertyP_prob` and `designPropertyP_prob`, used inside `sigma_unconditional_prob` for `prob.w = 1` |

## Hypotheses

No hypothesis is assumed in the w = 1 bundles `ft_fixedWeight`, `ft_virasoro`, `ft_n1`: each conjunct is
proved. `ft_fixedWeight_general` and `ft_fixedWeight_H3` take `(H3)` only where stated (`ft_fixedWeight_H3` takes
`TheoremC15UpperInput prob` as an explicit argument, as in `corollary_E1`). The concrete tests `g` in `FTLiminf`
and `FTRigidity` are quantified over every family satisfying the stated eventual feasibility; they are not
assumptions about `prob`.

## Axioms

Each bundle theorem is pinned to `[propext, Classical.choice, Quot.sound]` below.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Metric

universe u

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightTip
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Ramped FormalResearch.ModularBootstrap.TipFront
  FormalResearch.ModularBootstrap.FixedWeightBand FormalResearch.Special FormalResearch.ArgPrinciple

/-- **Lower bound (C1, C3, O(1) form).** Unconditional for every fixed-weight problem. -/
abbrev FTLower (prob : FixedWeightProblem) : Prop :=
  FixedWeightLowerBoundInput prob

/-- **Airy coefficient, liminf (C2 first clause).** For every family of concrete weakly feasible tests
`g_n` at scales `c'_n → ∞`, `liminf (T(g_n) − ξ̄c̃)c̃^{-1/3} ≥ A_opt`, with `leastThreshold` the threshold of `g_n`. -/
def FTLiminf (prob : FixedWeightProblem) : Prop :=
  ∀ {ι : Type u} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated] {c' : ι → ℝ},
    Tendsto c' p atTop → ∀ g : ι → ℝ → ℝ,
      (∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n)) →
        (Aopt : EReal) ≤ Filter.liminf (fun n =>
          (((leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p

/-- **Rigidity (C5a, C5b).** For every family `g_n` of concrete tests that is feasible at thresholds
`T_up n` with `(T_up n − ξ̄c')c'^{-1/3} → A_opt` (so that `Att` holds), the blow-up profile converges
(`R1`, `R2`, the `L¹` and locally uniform statements) and the zero counts converge to the nodes (`R3`). -/
def FTRigidity (prob : FixedWeightProblem) : Prop :=
  ∀ {ι : Type u} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated] {c' : ι → ℝ}
    (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ) (T_up : ι → ℝ),
    Tendsto (fun n => (T_up n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds Aopt) →
    ∀ hg_up : ∀ᶠ n in p, ∃ T : ℝ, 0 ≤ T ∧ T ≤ T_up n ∧ prob.IsWeaklyFeasible (c' n / 12) T (g n),
      let hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n) :=
        hg_up.mono fun _ ⟨T, _, _, hwf⟩ => ⟨T, hwf⟩
      let F := blowupFamilyPackage_of_concrete_tests_general prob hc' g hg
      let R := rigidityFamilyPackage_of_concrete_tests_general prob hc' g hg
      (Tendsto F.s₁ p (nhds s1) ∧
        TendstoLocallyUniformlyOn F.Φ phiStar p univ ∧ Tendsto F.γ p (nhds 0)) ∧
      ((Tendsto (fun n => ∫ s : ℝ, ‖phiExt R n s - phiStar (s : ℂ)‖) p (nhds 0) ∧
        Tendsto (fun n => ∫ s in Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ)),
          ‖R.Φ n (s : ℂ) - phiStar (s : ℂ)‖) p (nhds 0) ∧
        (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧
          ∀ᶠ n in p, ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖ < ε) ∧
        Tendsto (fun R₀ : ℝ => Filter.limsup (fun n => ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖) p)
          atTop (nhds 0))) ∧
      ((∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
        zeroCount (R.Φ n) (s1 : ℂ) r = 1 ∧ (R.s₁ n : ℂ) ∈ ball (s1 : ℂ) r ∧
        R.Φ n (R.s₁ n : ℂ) = 0 ∧ analyticOrderNatAt (R.Φ n) (R.s₁ n : ℂ) = 1 ∧
        ∀ z ∈ ball (s1 : ℂ) r, R.Φ n z = 0 → z = (R.s₁ n : ℂ)) ∧
      (∀ k : ℕ, 2 ≤ k → ∃ r₀ > 0,
        (∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
          zeroCount (R.Φ n) (sNode k : ℂ) r = 2 ∧
          ((∃ x : ℝ, (x : ℂ) ∈ ball (sNode k : ℂ) r ∧ R.Φ n (x : ℂ) = 0 ∧
              analyticOrderNatAt (R.Φ n) (x : ℂ) = 2 ∧
              ∀ z ∈ ball (sNode k : ℂ) r, R.Φ n z = 0 → z = (x : ℂ)) ∨
           (∃ z : ℂ, z ∈ ball (sNode k : ℂ) r ∧ z.im ≠ 0 ∧ R.Φ n z = 0 ∧
              R.Φ n (starRingEnd ℂ z) = 0 ∧ analyticOrderNatAt (R.Φ n) z = 1 ∧
              analyticOrderNatAt (R.Φ n) (starRingEnd ℂ z) = 1 ∧
              ∀ w ∈ ball (sNode k : ℂ) r, R.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z))) ∧
        (∀ z : ι → ℂ, (∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0) →
          Tendsto z p (nhds (sNode k : ℂ)) ∧
          Tendsto (fun n => (tScale (R.c' n) (z n) - ((xiBar * R.c' n : ℝ) : ℂ)) /
              (((R.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p
            (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) ∧
          (k = 2 →
            Tendsto (fun n => (tScale (R.c' n) (z n) - (R.t₁ n : ℂ)) /
                ((((R.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ))) p
              (nhds ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ))))) ∧
        (∃ z : ι → ℂ, ∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0)) ∧
      (∀ K : Set ℂ, IsCompact K → (∀ k : ℕ, 1 ≤ k → (sNode k : ℂ) ∉ K) →
        ∀ᶠ n in p, ∀ z ∈ K, R.Φ n z ≠ 0))

/-- **Airy law (C2 full under H3, C4).** The two-sided `O(1)` law at fixed weight, as the conclusion of
`FixedWeight.corollary_E1`: `T_V = T_* + O(1)` with the extremal measure and the `(Gap)` clause. -/
def FTAiryLaw (prob : FixedWeightProblem) : Prop :=
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
        atTop (𝓝 0))

/-- **Extremal measures (C5c), Airy level only.** Theorem `Σ` of `sr:Sigma`, at fixed weight one (`N = Ai`); not the paper's
C5(c) at every Hermite–Biehler level. -/
def FTSigma (prob : FixedWeightProblem) : Prop :=
  ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
    ∃ S : CrossingSequence prob, S.c = cSeq ∧
      (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
      (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
      SigmaConclusion S.μS

/-- **FT, fixed-weight families, every `prob`**: the lower bound, the liminf (C2), and the rigidity
statements (C5a, C5b) hold for every fixed-weight problem with no hypothesis. -/
theorem ft_fixedWeight_general (prob : FixedWeightProblem) :
    FTLower prob ∧ FTLiminf.{u} prob ∧ FTRigidity.{u} prob := by
  refine ⟨fixedWeightLowerBoundInput_of_problem prob, ?_, ?_⟩
  · unfold FTLiminf
    intro ι p _ _ c' hc' g hg
    exact concrete_blowup_theorem_C_general prob hc' g hg
  · unfold FTRigidity
    intro ι p _ _ c' hc' g T_up hT_lim hg_up
    have hAtt := att_of_upper_threshold_general prob hc' g T_up hT_lim hg_up
    exact ⟨concrete_blowup_theorem_R1_general prob hc' g _ hAtt,
      concrete_blowup_theorem_R2_general prob hc' g _ hAtt,
      concrete_blowup_theorem_R3_general prob hc' g _ hAtt⟩

/-- **FT, C2 full and C4 under the attainment hypothesis (H3).** -/
theorem ft_fixedWeight_H3 (prob : FixedWeightProblem) (hHi : TheoremC15UpperInput prob) :
    FTAiryLaw prob :=
  corollary_E1 prob (fixedWeightLowerBoundInput_of_problem prob) hHi

/-- **FT bundle for a weight-one fixed-weight problem.** Conjunction of the unconditional lower bound,
the liminf (C2), the rigidity (C5a, C5b), the two-sided Airy law (C2 full, C4, with H3 discharged by
Lemma `U*`) and the extremal-measure theorem (C5c). -/
theorem ft_fixedWeight (prob : FixedWeightProblem) (hw : prob.w = 1) :
    FTLower prob ∧ FTLiminf.{u} prob ∧ FTRigidity.{u} prob ∧ FTAiryLaw prob ∧ FTSigma prob :=
  ⟨fixedWeightLowerBoundInput_of_problem prob, (ft_fixedWeight_general.{u} prob).2.1,
    (ft_fixedWeight_general.{u} prob).2.2,
    ft_fixedWeight_H3 prob (theoremC15UpperInput_prob prob hw),
    sigma_unconditional_prob prob hw (fixedWeightLowerBoundInput_of_problem prob)⟩

/-- **FT bundle at Virasoro** (`w = 1`), no hypothesis. -/
theorem ft_virasoro : FTLower virasoroProblem ∧ FTLiminf.{u} virasoroProblem ∧
    FTRigidity.{u} virasoroProblem ∧ FTAiryLaw virasoroProblem ∧ FTSigma virasoroProblem :=
  ft_fixedWeight virasoroProblem virasoroProblem_w

/-- **FT bundle at `𝒩 = 1` super-Virasoro** (`w = 1`), no hypothesis. -/
theorem ft_n1 : FTLower n1SuperVirasoroProblem ∧ FTLiminf.{u} n1SuperVirasoroProblem ∧
    FTRigidity.{u} n1SuperVirasoroProblem ∧ FTAiryLaw n1SuperVirasoroProblem ∧
    FTSigma n1SuperVirasoroProblem :=
  ft_fixedWeight n1SuperVirasoroProblem n1SuperVirasoroProblem_w

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight_general

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight_H3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight_H3

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_virasoro

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_n1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_n1

end FormalResearch.ModularBootstrap.FoldTip
