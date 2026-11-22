module

public import FormalResearch.ModularBootstrap.Crossing.Bridge
public import FormalResearch.ModularBootstrap.SlitStrip.PoissonJensenInput
public import FormalResearch.ModularBootstrap.PoissonJensen.LemmaPJAssembly

/-!
# Theorem A for the optimal Virasoro gap, unconditional

Source: `CFT/modular_bootstrap/paper/log_free_optimality.tex`, Theorem A; inputs
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G (`vlo:Gap`) and Lemma PJ (`vlo:PJ`).

`Crossing.theorem_A_Delta_best` needs a `VirasoroStripInput`, i.e. the geometric data of the slit strip
and the analytic input `LemmaPJInput`.  (The deep-lobe estimate `LemmaGapInput` is derived from
`LemmaPJInput` inside `Crossing.Bridge`, by `lemmaGapInput_of_lemmaPJInput` of `Crossing.GapFromPJ`, so
that the `FixedGapInput` constants are produced, not assumed.)  Here:

* the geometry is the proved one: `rs = realSliceData` (`SlitStrip.RealSlice`), `U = majorantReal` with
  `(G-deficit)` proved (`majorantReal_g_deficit`, `SlitStrip.Majorant`);
* `StripPoissonJensen` (`∃ c_PJ C_PJ, 1 ≤ c_PJ ∧ LemmaPJInput realSliceData c_PJ C_PJ majorantReal`) is
  now **proved** by `PoissonJensen.stripPoissonJensen` (`PoissonJensen.LemmaPJAssembly`), combining
  Hankel inversion and strip holomorphy/continuity (`PoissonJensen.HankelInversion`), upper half-plane
  Poisson--Jensen (`PoissonJensen.HalfPlaneJensen`), harmonic-majorant identification `h = U`
  (`PoissonJensen.HarmonicMajorant`), and slit-mass/entropy estimates (`PoissonJensen.SlitMassAndDensity`).

Headlines:
* `virasoroStripInputOfPJ`: the `VirasoroStripInput` built from `LemmaPJInput` alone;
* `stripPoissonJensen`: **Lemma PJ** (`vlo:PJ`) for the real slit strip (`StripPoissonJensen`), proved;
* `theoremA_T_weak`, `theoremA_T_V`: `T_weak(c'), T_V(c') ≥ ξ̄ c' - C_A c'^{1/3}` for `c' ≥ c_A`;
* `theoremA_Delta_best`: **Theorem A for the optimal gap**, `Δ_best(c') ≥ c'/Λ_V - C_A c'^{1/3}`.
All three are unconditional (depend only on standard Lean axioms `[propext, Classical.choice, Quot.sound]`).
`testClass_exists_nonzero` shows that the quantification in `LemmaPJInput` is over a non-empty class.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.Integration

open Crossing

/-- **Lemma PJ for the actual slit strip (`vlo:PJ`), proved.**
There are constants `c_PJ ≥ 1`, `C_PJ` such that for every `c' ≥ c_PJ` and every nonzero concrete test
`g ∈ TestClass virasoroProblem (c'/12)` and every `x ∈ [0, ξ_*)`,
`log |g(c' x²/3)| ≤ c' U(x) + log M[g] - ½ log c' + (5/2)(1 - m(x)) log c' + S(x) + C_PJ`,
with `U = majorantReal` the harmonic majorant and `m, S` the slit mass and entropy of `realSliceData`.
Proved unconditionally in `PoissonJensen.stripPoissonJensen`. -/
def StripPoissonJensen : Prop :=
  ∃ c_PJ C_PJ : ℝ, 1 ≤ c_PJ ∧ LemmaPJInput realSliceData c_PJ C_PJ majorantReal

/-- **Lemma PJ for the real slit strip (`vlo:PJ`)**, proved in `PoissonJensen.LemmaPJAssembly`. -/
theorem stripPoissonJensen : StripPoissonJensen :=
  PoissonJensen.stripPoissonJensen

/-- The `VirasoroStripInput` built from `LemmaPJInput` for `realSliceData` and `majorantReal` alone:
`g_deficit` is proved. -/
noncomputable def virasoroStripInputOfPJ {c_PJ C_PJ : ℝ} (hc_PJ : 1 ≤ c_PJ)
    (hPJ : LemmaPJInput realSliceData c_PJ C_PJ majorantReal) : VirasoroStripInput :=
  { rs := realSliceData
    c_PJ := c_PJ
    C_PJ := C_PJ
    U := majorantReal
    hc_PJ := hc_PJ
    g_deficit := fun _ hx => majorantReal_g_deficit hx
    hPJ := hPJ }

/-- **Theorem A for `T_weak`** (`log_free_optimality.tex`), unconditional:
`T_weak(c') ≥ ξ̄ c' - C_A c'^{1/3}` for `c' ≥ c_A`. -/
theorem theoremA_T_weak :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_weak c' := by
  obtain ⟨c_PJ, C_PJ, hc, hPJ⟩ := PoissonJensen.stripPoissonJensen
  exact theorem_A_T_weak (virasoroStripInputOfPJ hc hPJ)

/-- **Theorem A for `T_V`** (`log_free_optimality.tex`), unconditional:
`T_V(c') ≥ ξ̄ c' - C_A c'^{1/3}` for `c' ≥ c_A`. -/
theorem theoremA_T_V :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_V c' := by
  obtain ⟨c_PJ, C_PJ, hc, hPJ⟩ := PoissonJensen.stripPoissonJensen
  exact theorem_A_T_V (virasoroStripInputOfPJ hc hPJ)

/-- **Theorem A for the optimal gap** (`log_free_optimality.tex`, Theorem A; `Δ_best(c') = T_V(c') + c'/12`),
unconditional: there are `C_A > 0` and `c_A ≥ 24` with `Δ_best(c') ≥ c'/Λ_V - C_A c'^{1/3}` for all `c' ≥ c_A`. -/
theorem theoremA_Delta_best :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      c' / lambdaV - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.Delta_best c' := by
  obtain ⟨c_PJ, C_PJ, hc, hPJ⟩ := PoissonJensen.stripPoissonJensen
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

/-- info: 'FormalResearch.ModularBootstrap.Integration.stripPoissonJensen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripPoissonJensen

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
