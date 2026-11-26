module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodMain
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScaleBridge

/-!
# `cts:lower-main` at spinless Virasoro (FIVE-L): the corollary of the skeleton

* `lowerPrelim_virasoro`: `LowerPrelim virasoroProblem` from `corL_virasoro` (`rem:corL`), `lemmaQ_part1`, `lemmaQ_part3`
  and `psiTilde_virasoroProblem`;
* `lowerPhase_virasoro`: `LowerMainInputs virasoroProblem c0Star gamma0` gives `LowerPhaseStatement virasoroProblem c0Star gamma0 C`
  (uses `c0Star_neg`);
* `spinless_lower_of_inputs`: **the lower half of `thm:spinless-expansion`**,
  `Δ_best(c) ≥ c/Λ_V + A_opt c^{1/3} + c_0^* + c_1^Langer c^{-1/3} + d_2^* c^{-2/3} - C_- c^{-1} log c`,
  modulo the named structure `LowerMainInputs` (the open lemmas `cts:cauchy-dual`, `cts:rosc-uncond`, `ctl:pass2`,
  `cts:boas` and the Langer identification), via the unconditional chart conversion `spinless_lower_of_phase`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Complex Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.FixedWeightBand

/-- `LowerPrelim` at spinless Virasoro: `rem:corL` (`corL_virasoro`), `lemmaQ_part1`, `lemmaQ_part3` and
`psiTilde_virasoroProblem`. -/
theorem lowerPrelim_virasoro : LowerPrelim virasoroProblem := by
  obtain ⟨c₁, K, hc₁, hK0, hcorL⟩ := corL_virasoro
  obtain ⟨cQ1, Cg, κg, hcQ1, hCg, hκg, hQ1⟩ := lemmaQ_part1
  have ha1 : airyZero 1 < 0 := airyZero_neg 1
  have hBV := virasoroBV_pos
  have hev : ∀ᶠ c : ℝ in atTop, |airyZero 1| ≤ virasoroAC c ^ 2 ∧ 0 < c := by
    have hc23 : Tendsto (fun c : ℝ => 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (by positivity)
    filter_upwards [hc23.eventually_ge_atTop |airyZero 1|, eventually_gt_atTop (0 : ℝ)] with c h1 h2
    exact ⟨by rwa [virasoroAC_sq c h2.le], h2⟩
  obtain ⟨c₃, hc₃⟩ := eventually_atTop.1 hev
  refine ⟨max (max c₁ cQ1) c₃, quantC1KappaStar, quantC1KappaStar_pos, fun c hc T g hg hTa => ?_⟩
  have hcc₁ : c₁ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hccQ : cQ1 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcc₃ : c₃ ≤ c := (le_max_right _ _).trans hc
  obtain ⟨hAa, hc0⟩ := hc₃ c hcc₃
  have hcEnv : virasoroCQEnv ≤ c := hc₁.trans hcc₁
  obtain ⟨-, -, -, hT_A2⟩ := hQ1 hccQ hg
  have hsA : StrictAntiOn (virasoroDeltaChart c) (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)) :=
    virasoroDeltaChart_strictAnti hc0
  have ha1_mem : airyZero 1 ∈ Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) := by
    exact abs_le.1 hAa
  have hnegA_mem : -(virasoroAC c ^ 2) ∈ Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) :=
    ⟨le_rfl, by linarith [sq_nonneg (virasoroAC c)]⟩
  have hnegA_le : -(virasoroAC c ^ 2) ≤ airyZero 1 := ha1_mem.1
  have hT_lt_neg : T < virasoroDeltaChart c (-(virasoroAC c ^ 2)) := by
    rcases hnegA_le.lt_or_eq with hlt | heq
    · exact hTa.trans (hsA hnegA_mem ha1_mem hlt)
    · rw [← heq] at hTa; exact hTa
  have hu_mem := virasoroUT_between hc0 (a := -(virasoroAC c ^ 2)) (b := virasoroAC c ^ 2) le_rfl le_rfl
    (by linarith [sq_nonneg (virasoroAC c)]) hT_A2.le hT_lt_neg.le
  obtain ⟨hlt1, -, -, -, hslope⟩ := (hcorL hcc₁ hg).2 hTa
  have hQ3 := lemmaQ_part3 hcEnv hg
  have hpsi : psiTilde virasoroProblem c g = virasoroPsiTilde c g := funext fun u =>
    psiTilde_virasoroProblem hc0.le g u
  refine ⟨⟨hlt1, hu_mem.1, hu_mem.2⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact psiTilde_im_ofReal virasoroProblem hc0 hg.1 hx
  · intro x hx hxu
    rw [hpsi]
    refine hQ3.1 x hx ?_
    rw [← hu_mem.2]
    exact hsA.antitoneOn (abs_le.1 hx) hu_mem.1 hxu
  · intro θ hθ0 hθ1
    rw [hpsi]
    exact hslope θ hθ0 hθ1

/-- `LowerPhaseStatement` at Virasoro from the open lemmas, with `LowerFirstGood` discharged
unconditionally from `h.chart` via `lowerFirstGood_of_chart_on_band`. -/
theorem lowerPhase_virasoro (h : LowerMainInputs virasoroProblem c0Star gamma0) :
    ∃ C : ℝ, 0 ≤ C ∧ LowerPhaseStatement virasoroProblem c0Star gamma0 C := by
  obtain ⟨cc, C, hfg⟩ := lowerFirstGood_of_chart_on_band c0Star gamma0 h.c1 h.phi h.uhat
    h.c1_pos h.c1_small h.chart
  exact lowerPhase_of_inputs c0Star_neg lowerPrelim_virasoro h
    ⟨cc, C, fun c hc T g hg _ hT_hi => hfg c hc T g hg hT_hi⟩

/-- **Lower half of `thm:spinless-expansion`, modulo `LowerMainInputs`** (`cts:lower-main`, Theorem C9):
`Δ_best(c) ≥ c/Λ_V + A_opt c^{1/3} + c_0^* + c_1^Langer c^{-1/3} + d_2^* c^{-2/3} - C_- c^{-1} log c`. -/
theorem spinless_lower_of_inputs (h : LowerMainInputs virasoroProblem c0Star gamma0) :
    ∃ Cm c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c →
      c / lambdaV + Aopt * c ^ (1 / 3 : ℝ) + c0Star + c1Langer * c ^ (-(1 / 3) : ℝ) +
        d2Star * c ^ (-(2 / 3) : ℝ) - Cm * c ^ (-1 : ℝ) * Real.log c ≤
      virasoroProblem.Delta_best c := by
  obtain ⟨C, hC, hL⟩ := lowerPhase_virasoro h
  exact spinless_lower_of_phase c0Star gamma0 C hC hL

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerPrelim_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerPrelim_virasoro

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.spinless_lower_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.spinless_lower_of_inputs
