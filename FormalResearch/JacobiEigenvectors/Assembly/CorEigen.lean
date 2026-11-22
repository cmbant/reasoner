module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.ThmAi
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenWindows
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenS1
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenInverseSlope
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenCount
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenGapM

/-!
# Paper J: cor:eigen (a)-(d) proved from the Layer-4 chart inputs (L2.E)

Source: Paper J `main_results.tex`, `cor:eigen`; proof in `thmA.tex`, Section "Inverse quantisation, gaps and counting"; frozen statement `CorEigen` of `TheoremA/EigenvalueStatements.lean`.

## Proved here (axiom-pinned)

* `actionS0_frozen_trunc_one`: the principal-symbol action of the frozen truncation `truncSM G 1` is that of `frozenFamily G 0` (`G_0 + t G_1`, `B_0 + t B_1`).
* `bandSlope_of_layer4`: the slope input `BandSlope G K S` (`-S_0' >= 2 c_0` on the closed band) for *every* `S` with `SmoothExt` and `ActionFormula`, from the windows of the assembly (`layer4_windows`, `bandSlope_of_windows_trunc`).  The slope depends on `S` only through
  `S_0 = actionS0 G` on the band, so one set of windows (at any order `M'`) serves every `S` and every `M`.
* **`corEigen_proved : CorEigen G K M`**, the frozen statement (cor:eigen (a)-(d), with `0 < delta` added to (a), (b), (c), (d), finding F-BB-1), from the Layer-4 inputs below and **no further premise** (in particular no `BandSlope`, finding F-BB-2):
  * (a) `CorEigenS1`: `corEigenS1_of_trunc_windows` with the windows of order `1`, whose chart-level premises (`Sigma_1(X, 0) = 0`, `Sigma_0 = S_0^{(t)}` for `t` near `0`) are discharged by `layer4_windows` for the bulk blocks (`BulkPhaseInputs.Sigma_one`, `Sigma_zero`), the upper soft
    window (`softSigma_zero_eventually`: the chart's `mu0_S0` at `(mu, t)`) and the lower soft window (`softLoSigma_zero_eventually`: the same through the mirror family, `actionS0_neg`);
  * (b) `CorEigenInverse`: `corEigenInverse_of_slope` with `bandSlope_of_layer4` at order `1`;
  * (c) `CorEigenGap1`: `corEigenGap1_of_slope`; `CorEigenGapM`: `corEigenGapM` (needs only `InvExpansion`);
  * (d) `CorEigenCount`: `corEigenCount_of_slope`, with the slope from the windows of order `0` (the statement is under `(D_0)` only).

## The Layer-4 inputs of `corEigen_proved` (the only premises besides the statement's own)

`Layer4Inputs G K 0` and `Layer4Inputs G K 1` (`Assembly/ThmAi.lean`), i.e. for `M' in {0, 1}` (`Kidx = (M' + 1)/2`, the chart order `max M' 1` and `q = 2 Kidx`) exactly the premises of `thmAi_assembled`:
* `CI`: the chart inputs of `truncFamily G M'` (`ChartInputs`: parabolic-cylinder facts, the bulk Weber blocks, the upper and lower soft charts and their mirrors, the cover);
* `PI`: the bulk phase inputs of every block (`BulkPhaseInputs`: phase `Sigma`, its `C^{2M'+1}` regularity, `Sigma_0` the action, `Sigma_1 = 0`, the Casoratian, the uniform norm bound);
* `SIu`, `SIl`: the soft phase inputs of the two band ends (`SoftPhaseInputs`) with a common half-width `SIl.w = SIu.w`;
* `ht0 : 0 < t0`, `hKidx`, and the geometric relations of the cover `hlt`, `hJhi`, `hJlo`, `hwb`.

Order `1` is used for (a), (b), (c) (`DM G K 1` follows from `DM G K M`, `1 <= M`); order `0` for (d), which has only `(D_0)`.  (For `M = 0` the statements (b), (c)-general are vacuous and (a), (c)-first carry their own `DM G K 1`.)

## Differences from the paper

* `0 < delta` is a premise of (a), (b), (c) first part and (d) (F-BB-1; the paper's `S_j` live on a `delta`-neighbourhood, `delta > 0`).
* The slope `-S_0' >= 2 c_0` is not an input: the paper computes `S_0' = -int T^{-1/2}`; here it is read off the glued windows (`bandSlope_of_windows`), which carry `partial_X Sigma_0(., 0) <= -c`.
* `CorEigenInverse` (iii) uses no implicit function theorem (see `CorEigenGapM.lean`).

## Not formalised

The Layer-4 inputs themselves (`CI`, `PI`, `SIu`, `SIl`; `thm:smo-MPS/TPC/WT2`, the Weber and parabolic-cylinder charts), and the existence of the soft half-width `w` meeting the geometric relations of the cover.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- The action of the frozen truncation `truncSM G 1` is that of `frozenFamily G 0`: both are the action of the principal symbols `G_0 + t G_1`, `B_0 + t B_1`. -/
lemma actionS0_frozen_trunc_one (G : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (t X : ℝ) :
    actionS0 (frozenFamily (truncSM G 1) Kidx) (μ, t) X = actionS0 (frozenFamily G 0) (μ, t) X := by
  unfold actionS0
  simp only [frozen_G0, frozen_B0]
  simp [truncSM, frozenFamily]

/-- **The slope input from the Layer-4 inputs**: for every `S` with `SmoothExt G K M S delta_1 Cn` (`0 < delta_1`) and `ActionFormula G K S`, `BandSlope G K S`; the windows are those of `layer4_windows` of any order `M'`. -/
theorem bandSlope_of_layer4 {G : SymbolFamily Par} {K : Set Par} {M' M : ℕ} (L : Layer4Inputs G K M') (hK : IsCompact K) (hH : HypOn G K)
    (hD' : DM G K M') {S : ℕ → Par → ℝ → ℝ} {δ1 Cn : ℝ} (hδ1 : 0 < δ1) (hS : SmoothExt G K M S δ1 Cn) (hA : ActionFormula G K S) :
    BandSlope G K S := by
  obtain ⟨ι, hι, a, b, t0', δ, W, ht0', hδ, hcov, -, -⟩ := layer4_windows L hK hH hD'
  exact bandSlope_of_windows_trunc W hδ hcov (bandLo_lt_bandHi G K M' hH hD') hδ1 hS hA

/-- **cor:eigen (a)-(d)** (`CorEigen`, the frozen statement with `0 < delta`, F-BB-1) from the Layer-4 inputs of orders `0` and `1` (see the module docstring) and no further premise. -/
theorem corEigen_proved (G : SymbolFamily Par) (K : Set Par) (M : ℕ) (L0 : Layer4Inputs G K 0) (L1 : Layer4Inputs G K 1) :
    CorEigen G K M := by
  refine ⟨?_, ?_, ?_, corEigenGapM G K M, ?_⟩
  · -- (a)
    intro hK hH hD S δ Cn hM C hδ hS hR hA μ hμ X hX
    obtain ⟨ι, hι, a, b, t0', δw, W, ht0', hδw, hcov, hone, hzero⟩ := layer4_windows L1 hK hH hD
    have hb := band_truncSM G 1
    refine corEigenS1_of_trunc_windows W ht0' hδw hcov ?_ ?_ hK hH hD S δ Cn hM C hδ hS hR hA μ hμ X hX
    · intro i μ hμ X hXi hXb
      exact hone i μ hμ X hXi (by rw [(hb μ).1, (hb μ).2]; exact hXb)
    · intro i μ hμ X hXi hXb
      have h := hzero le_rfl i μ hμ X hXi (by rw [(hb μ).1, (hb μ).2]; exact hXb)
      refine h.mono fun t ht => ?_
      rw [ht, actionS0_frozen_trunc_one]
  · -- (b)
    intro hM1 hK hH hD S δ Cn hM C hδ hS hR hA
    have hD1 : DM G K 1 := dm_mono G K hM1 hK hD
    exact corEigenInverse_of_slope hK hH hD hM1 hδ hS hR hA (bandSlope_of_layer4 L1 hK hH hD1 hδ hS hA)
  · -- (c), first part
    intro hK hH hD S δ Cn hM C hδ hS hR hA x0 hx0
    exact corEigenGap1_of_slope hK hH hD hδ hS hR hA (bandSlope_of_layer4 L1 hK hH hD hδ hS hA) x0 hx0
  · -- (d)
    intro hK hH hD S δ Cn hM C hδ hS hR hA
    exact corEigenCount_of_slope G K hK hH hD S δ Cn hM C hδ hS hR hA (bandSlope_of_layer4 L0 hK hH hD hδ hS hA)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bandSlope_of_layer4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bandSlope_of_layer4

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigen_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigen_proved

end FormalResearch.JacobiEigenvectors.TheoremA

end
