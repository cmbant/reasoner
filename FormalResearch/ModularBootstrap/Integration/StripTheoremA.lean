module

public import FormalResearch.ModularBootstrap.Integration.GapFromPJ
public import FormalResearch.ModularBootstrap.SlitStrip.PoissonJensenInput

/-!
# Theorem A for the optimal Virasoro gap, with the proved slit-strip geometry

Source: `CFT/modular_bootstrap/paper/log_free_optimality.tex`, Theorem A; inputs
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G (`vlo:Gap`) and Lemma PJ (`vlo:PJ`).

`Crossing.theorem_A_Delta_best` needs a `VirasoroStripInput`, i.e. the geometric data of the slit strip
*and* the two unproved analytic inputs `LemmaPJInput` and `LemmaGapInput`.  Here:

* the geometry is the proved one: `rs = realSliceData` (`SlitStrip.RealSlice`), `U = majorantReal` with
  `(G-deficit)` proved (`majorantReal_g_deficit`, `SlitStrip.Majorant`);
* `LemmaGapInput` is no longer an input: it is derived from `LemmaPJInput` (`lemmaGapInput_of_lemmaPJInput`,
  `Integration.GapFromPJ`), so that the `FixedGapInput` constants are produced, not assumed;
* the single remaining analytic hypothesis is `StripPoissonJensen`: Lemma PJ for the actual slit strip,
  `∃ c_PJ C_PJ, 1 ≤ c_PJ ∧ LemmaPJInput realSliceData c_PJ C_PJ majorantReal`.

Headlines:
* `virasoroStripInputOfPJ`: the `VirasoroStripInput` built from `LemmaPJInput` alone;
* `theoremA_T_weak`, `theoremA_T_V`: `T_weak(c'), T_V(c') ≥ ξ̄ c' - C_A c'^{1/3}` for `c' ≥ c_A`;
* `theoremA_Delta_best`: **Theorem A for the optimal gap**, `Δ_best(c') ≥ c'/Λ_V - C_A c'^{1/3}`.
All three are conditional on `StripPoissonJensen` only.

Not covered: a proof of `StripPoissonJensen` (the Poisson--Jensen inequality for the Hankel continuation
`G` on the slit strip, with its Bessel inputs, `lower_o1_two_edge.tex` Lemma PJ).  Its ingredients in
this development: the harmonic-measure identification `h = U` (`HarmonicMajorantIdentification`, not
proved), the continuation `G` and its strip bound (Lemma B (d), second bound; see `Integration.StripKernel`),
and the Poisson--Jensen inequality for `log |G|` (no Mathlib support).
`testClass_exists_nonzero` shows that the quantification in `LemmaPJInput` is over a non-empty class.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.Integration

open Crossing

/-- **Lemma PJ for the actual slit strip (`vlo:PJ`), the single remaining analytic hypothesis.**
There are constants `c_PJ ≥ 1`, `C_PJ` such that for every `c' ≥ c_PJ` and every nonzero concrete test
`g ∈ TestClass virasoroProblem (c'/12)` and every `x ∈ [0, ξ_*)`,
`log |g(c' x²/3)| ≤ c' U(x) + log M[g] - ½ log c' + (5/2)(1 - m(x)) log c' + S(x) + C_PJ`,
with `U = majorantReal` the harmonic majorant and `m, S` the slit mass and entropy of `realSliceData`.
Not proved here. -/
def StripPoissonJensen : Prop :=
  ∃ c_PJ C_PJ : ℝ, 1 ≤ c_PJ ∧ LemmaPJInput realSliceData c_PJ C_PJ majorantReal

/-- The `VirasoroStripInput` built from `LemmaPJInput` for `realSliceData` and `majorantReal` alone:
`g_deficit` is proved and the deep-lobe estimate is derived (`lemmaGapInput_of_lemmaPJInput`). -/
noncomputable def virasoroStripInputOfPJ {c_PJ C_PJ : ℝ} (hc_PJ : 1 ≤ c_PJ)
    (hPJ : LemmaPJInput realSliceData c_PJ C_PJ majorantReal) : VirasoroStripInput :=
  let hgap := lemmaGapInput_of_lemmaPJInput realSliceData majorantReal hc_PJ
    (fun _ hx => majorantReal_g_deficit hx) hPJ
  { rs := realSliceData
    c_PJ := c_PJ
    C_PJ := C_PJ
    U := majorantReal
    hc_PJ := hc_PJ
    g_deficit := fun _ hx => majorantReal_g_deficit hx
    fg := hgap.choose
    hPJ := hPJ
    hDeepLobe := hgap.choose_spec }

/-- **Theorem A for `T_weak`** (`log_free_optimality.tex`), conditional only on Lemma PJ for the slit
strip (`StripPoissonJensen`): `T_weak(c') ≥ ξ̄ c' - C_A c'^{1/3}` for `c' ≥ c_A`. -/
theorem theoremA_T_weak (h : StripPoissonJensen) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_weak c' := by
  obtain ⟨c_PJ, C_PJ, hc, hPJ⟩ := h
  exact theorem_A_T_weak (virasoroStripInputOfPJ hc hPJ)

/-- **Theorem A for `T_V`** (`log_free_optimality.tex`), conditional only on `StripPoissonJensen`:
`T_V(c') ≥ ξ̄ c' - C_A c'^{1/3}` for `c' ≥ c_A`. -/
theorem theoremA_T_V (h : StripPoissonJensen) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_V c' := by
  obtain ⟨c_PJ, C_PJ, hc, hPJ⟩ := h
  exact theorem_A_T_V (virasoroStripInputOfPJ hc hPJ)

/-- **Theorem A for the optimal gap** (`log_free_optimality.tex`, Theorem A; `Δ_best(c') = T_V(c') + c'/12`):
conditional only on Lemma PJ for the slit strip (`StripPoissonJensen`), there are `C_A > 0` and
`c_A ≥ 24` with `Δ_best(c') ≥ c'/Λ_V - C_A c'^{1/3}` for all `c' ≥ c_A`. -/
theorem theoremA_Delta_best (h : StripPoissonJensen) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      c' / lambdaV - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.Delta_best c' := by
  obtain ⟨c_PJ, C_PJ, hc, hPJ⟩ := h
  exact theorem_A_Delta_best (virasoroStripInputOfPJ hc hPJ)

/-- Non-vacuity of the quantifier in `LemmaPJInput`/`StripPoissonJensen`: for every `c' ≥ 24`
the test class `TestClass virasoroProblem (c'/12)` contains a function with `M[g] > 0`. -/
theorem testClass_exists_nonzero {c' : ℝ} (hc : 24 ≤ c') :
    ∃ g : ℝ → ℝ, TestClass virasoroProblem (c' / 12) g ∧
      0 < virasoroProblem.cardyNorm (c' / 12) g := by
  have hshift : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith
  have hsh : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  obtain ⟨T, _, g, hg⟩ := virasoroProblem.feasible_nonempty hshift
  exact ⟨g, hg.isWeaklyFeasible.1, cardyNorm_pos_of_nonzero hsh hg.isWeaklyFeasible.1
    hg.isWeaklyFeasible.2.1⟩

/-- info: 'FormalResearch.ModularBootstrap.Integration.theoremA_Delta_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremA_Delta_best

/-- info: 'FormalResearch.ModularBootstrap.Integration.theoremA_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremA_T_V

/-- info: 'FormalResearch.ModularBootstrap.Integration.theoremA_T_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremA_T_weak

/-- info: 'FormalResearch.ModularBootstrap.Integration.virasoroStripInputOfPJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroStripInputOfPJ

/-- info: 'FormalResearch.ModularBootstrap.Integration.testClass_exists_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms testClass_exists_nonzero

end FormalResearch.ModularBootstrap.Integration
