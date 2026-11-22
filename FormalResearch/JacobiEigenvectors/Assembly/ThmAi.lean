module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.ThmA
public import FormalResearch.JacobiEigenvectors.Assembly.SoftLabels
public import FormalResearch.JacobiEigenvectors.Assembly.WindowCoverProof
public import FormalResearch.JacobiEigenvectors.Assembly.Labels
public import FormalResearch.JacobiEigenvectors.Assembly.ChartRestrict
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenZero

/-!
# Paper J: thm:A (i) assembled from the Layer-4 inputs (L2.C9, items 1-4)

Source: Paper J `thmA.tex`, proof of `thm:A (i)` ("Location and labels", "Bulk phases", "Gluing"); frozen statement `ThmAi` (`TheoremA/Statements.lean`).

## Proved here (axiom-pinned)

* `thmAi_assembled`: `ThmAi G K M` from the chart data `CI` of `truncFamily G M` and the following premises only (all Layer-4 phase inputs or geometric relations of the cover).
  * `PI`: the bulk phase inputs of every block (`BulkPhaseInputs`: Weber charts and the phase `Sigma` with its regularity, zero data and uniform `C^{2M+1}` bound);
  * `SIu`, `SIl`: the soft phase inputs of the two band ends (`SoftPhaseInputs`: closeness `rho`, regularity of `X_s^+(t)` and `mu_{2r}`, the `C^{2M+1}` bound), with one common half-width `hw : SIl.w = SIu.w`;
  * `ht0 : 0 < t0`, `hKidx : Kidx = (M + 1) / 2`;
  * the geometric relations of the cover: `hlt` (blocks of positive length), `hJhi`, `hJlo` (the soft windows reach into the bulk range: `X_s^+ - w < J_hi`, `J_lo < X_s^- + w`; the uniform margin that the labels need is derived from the continuity of `X_s^+` in `mu` on the compact `K`), `hwb` (`w <= X_s^+ - X_s^-`).
  Everything else is proved: the standing assumptions `StdAssump` (obtained for `t0' = min t0 t1 t2`, the charts being restricted to it by `ChartInputs.restrict`, so the paper's "`t_0` small" is no premise),
  the soft labels `SoftLabels`, `SoftLabelsLo` (`SoftLabels.lean`), the soft windows `WS` (`softUpWindow`, `softLoWindow`), the cover `hcov` (`WindowCoverProof.lean`) and **the bulk labels `hlabels`**
  (`BulkWindowLabels`, `bulkLabels_core` in `Labels.lean`).
* `Layer4Inputs G K M`: the Layer-4 inputs of `thmAi_assembled` bundled in one structure.
* `layer4_windows`: the glued windows exposed: finitely many `WindowPhase (truncSM G M)` on a common `t0'` with a `WindowCover` (`delta = SIu.w`), together with the chart-level facts `cor:eigen` (a) needs (`Sigma_1(., 0) = 0` on the open band; for `1 <= M`, `Sigma_0 = actionS0 (frozenFamily (truncSM G M) Kidx) (mu, t)`
  for `t` near `0`: bulk from `BulkPhaseInputs.Sigma_one/Sigma_zero`, soft from `CorEigenZero.lean`).  `thmAi_assembled` is its glued consequence (`thmAi_of_windows`, `thmAi_of_trunc`); `corEigen_proved` (`Assembly/CorEigen.lean`) uses the windows.
* `thmA_of_layer4`: `ThmAi /\ ThmAii` (with `thmAii_proved`) for charts `CItr` (of `truncFamily G M`) and `CI` (of `G` at order `m`).

## The chain for the labels (paper, "Location and labels") and where it is proved

See `Assembly/Labels.lean`: windows and counting (`bulk_count`), consecutive windows by a Lebesgue number of the block cover and the quantitative slope at `t = h` (`LabelsAbstract.lean`, `LabelsSlope.lean`),
the anchor at the soft window `0` from `PropThaW2` (3) and `pi mu_0 = S_0` (`LabelsSoft.lean`), induction along the eigenvalue index.

## Differences from the paper

* `BulkWindowLabels` is stated at `t = h` only (the only case used).  The relations `hJhi`, `hJlo`, `hwb` are the choice of the soft half-width `w` against the cover (`w` large enough to reach into the bulk range, small enough for `w <= X_s^+ - X_s^-`); they cannot be derived from the chart fields, which do not constrain `w`.

## Not formalised

The Layer-4 inputs `PI`, `SIu`, `SIl` (the phase coefficients and their regularity, `thm:smo-MPS/TPC/WT2`) and the Layer-1 inputs behind the chart fields; the choice of `w` (existence of `w` meeting the geometric relations).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- The left and right ends of the four windows of the cover: bulk blocks are separate; `true` is the upper soft window `[X_s^+(mu, 0) - w, X_s^+(mu, 0) + w]`,
`false` the lower one `[X_s^-(mu) - w, X_s^-(mu) + w]` (the windows of `softUpWindow`, `softLoWindow`). -/
def softEnds (T : SymbolFamily Par) (Kidx : ℕ) (wu wl : ℝ) : (Bool → Par → ℝ) × (Bool → Par → ℝ) :=
  (fun s μ => match s with
      | true => (frozenFamily T Kidx).bandHi (μ, 0) - wu
      | false => T.bandLo μ - wl,
   fun s μ => match s with
      | true => (frozenFamily T Kidx).bandHi (μ, 0) + wu
      | false => T.bandLo μ + wl)

/-- The band end `mu -> X_s^+(mu)` is continuous on a compact `K` (`CoreReg.contBandHi`, from `(D_M)`), so a pointwise strict margin is uniform. -/
lemma uniform_margin_bandHi {T : SymbolFamily Par} {K : Set Par} {M : ℕ} (hK : IsCompact K) (hD : DM T K M) (w J : ℝ)
    (h : ∀ μ ∈ K, T.bandHi μ - w < J) : ∃ ε : ℝ, 0 < ε ∧ ∀ μ ∈ K, T.bandHi μ - w + ε ≤ J := by
  by_cases hKe : K.Nonempty
  · have hc : ContinuousOn (fun μ => T.bandHi μ) K :=
      continuousOn_iff_continuous_restrict.mpr (coreReg_of_DM hK hD).contBandHi
    obtain ⟨μ0, hμ0, hmin⟩ := hK.exists_isMinOn hKe (continuousOn_const.sub (hc.sub continuousOn_const) : ContinuousOn (fun μ => J - (T.bandHi μ - w)) K)
    refine ⟨J - (T.bandHi μ0 - w), by have := h μ0 hμ0; linarith, fun μ hμ => ?_⟩
    have := hmin hμ
    simp only [Set.mem_setOf_eq, Pi.sub_apply] at this
    linarith
  · exact ⟨1, one_pos, fun μ hμ => absurd ⟨μ, hμ⟩ hKe⟩

/-- **The Layer-4 inputs of `thmAi_assembled`, bundled** (so that the windows and the theorems built from them take them as one argument): the chart data `CI` of `truncFamily G M` at order `max M 1`, the bulk phase inputs `PI`, the soft phase inputs
`SIu`, `SIl` of the two band ends with a common half-width, and the geometric relations of the cover.  See the docstring of this file. -/
structure Layer4Inputs (G : SymbolFamily Par) (K : Set Par) (M : ℕ) where
  Kidx : ℕ
  t0 : ℝ
  U : ℝ → ℝ → ℝ
  V : ℝ → ℝ → ℝ
  cPC : ℝ
  CPC : ℝ
  CI : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC
  PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν)
  ht0 : 0 < t0
  SIu : SoftPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 M CI.softUpL
  SIl : SoftPhaseInputs (negFamily (frozenFamily (truncSM G M) Kidx)) (paramSet K t0) K t0 M CI.softLoL
  hw : SIl.w = SIu.w
  hlt : ∀ ν, CI.lo ν < CI.hi ν
  hJhi : ∀ μ ∈ K, (truncSM G M).bandHi μ - SIu.w < CI.Jhi
  hJlo : ∀ μ ∈ K, CI.Jlo < (truncSM G M).bandLo μ + SIu.w
  hwb : ∀ μ ∈ K, SIu.w ≤ (truncSM G M).bandHi μ - (truncSM G M).bandLo μ
  hKidx : Kidx = (M + 1) / 2

/-- **The phase windows of the assembly, from the Layer-4 inputs** (the windows that `thmAi_assembled` glues, exposed): for compact `K`, `(H1)`--`(H3)`, `(D_M)`, there are finitely many windows `W i` of `truncSM G M` on a common `t0'` (the bulk
blocks, then the upper and lower soft windows), covering `[X_s^- - delta, X_s^+ + delta]` with `0 < delta` (`WindowCover`), together with the two chart-level facts that `cor:eigen` (a) needs of every window phase:
`Sigma_1(X, 0) = 0` on the open band, and (for `1 <= M`) `Sigma_0(X, t) = S_0^{(t)}(X) = actionS0 (frozenFamily (truncSM G M) Kidx) (mu, t) X` for all `t` near `0`.  Everything is proved from the inputs, as in `thmAi_assembled`
(which is now the glued consequence of this lemma). -/
theorem layer4_windows {G : SymbolFamily Par} {K : Set Par} {M : ℕ} (L : Layer4Inputs G K M) :
    IsCompact K → HypOn G K → DM G K M →
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → Par → ℝ) (t0' δ : ℝ) (W : ∀ i, WindowPhase (truncSM G M) K t0' M (a i) (b i)),
      0 < t0' ∧ 0 < δ ∧ WindowCover (truncSM G M) K a b δ ∧
      (∀ i, ∀ μ ∈ K, ∀ X ∈ Icc (a i μ) (b i μ), X ∈ Ioo ((truncSM G M).bandLo μ) ((truncSM G M).bandHi μ) → (W i).Sigma μ 1 X 0 = 0) ∧
      (1 ≤ M → ∀ i, ∀ μ ∈ K, ∀ X ∈ Icc (a i μ) (b i μ), X ∈ Ioo ((truncSM G M).bandLo μ) ((truncSM G M).bandHi μ) →
        ∀ᶠ t in 𝓝 (0 : ℝ), (W i).Sigma μ 0 X t = actionS0 (frozenFamily (truncSM G M) L.Kidx) (μ, t) X) := by
  obtain ⟨Kidx, t0, U, V, cPC, CPC, CI, PI, ht0, SIu, SIl, hw, hlt, hJhi, hJlo, hwb, hKidx⟩ := L
  intro hK hH hD
  have hHT := hypOn_truncSM G K M hH
  have hDT := dm_truncSM G K M hD
  have hD0 : DM (truncSM G M) K 0 := dm_zero_of_dm _ K M hK hDT
  have hq : M ≤ 2 * Kidx := by omega
  -- the standing assumptions, on a smaller `t0'`
  obtain ⟨t1, ht1, hs1⟩ := stdAssump_trunc G K M Kidx hKidx hK hH hD
  obtain ⟨t2, ht2, hs2⟩ := HypMorse.frozenStandard_of_reg (truncSM G M) K Kidx (regBudget M) hK hHT (frozenReg_trunc G K M Kidx hKidx hD)
  set t0' : ℝ := min t0 (min t1 t2) with ht0'def
  have ht0' : 0 < t0' := lt_min ht0 (lt_min ht1 ht2)
  have hle0 : t0' ≤ t0 := min_le_left _ _
  have hle1 : t0' ≤ t1 := (min_le_right _ _).trans (min_le_left _ _)
  have hle2 : t0' ≤ t2 := (min_le_right _ _).trans (min_le_right _ _)
  have hstd' := hs1 t0' ht0' hle1
  have hstdK' : ∃ r, StdAssump (frozenFamily (truncSM G M) Kidx) (paramSet K t0') Kidx r :=
    ⟨regBudget M, stdAssump_restrict hs2 (paramSet_mono K hle2) (hK.prod isCompact_Icc)⟩
  have hPsub : paramSet K t0' ⊆ paramSet K t0 := paramSet_mono K hle0
  let CI' := CI.restrict hle0
  have hlab : SoftLabels (truncSM G M) Kidx K (max M 1) CI.softUpL :=
    softLabels_of_chart (T := truncSM G M) (M := max M 1) CI' ht0' (le_max_right _ _) le_rfl hstdK'
  have hlabW : SoftLabels (truncSM G M) Kidx K M CI.softUpL :=
    softLabels_of_chart (T := truncSM G M) (M := M) CI' ht0' (le_max_right _ _) (le_max_left _ _) hstdK'
  have hlabLo : SoftLabelsLo (truncSM G M) Kidx K M CI.softLoL :=
    softLabelsLo_of_chart (T := truncSM G M) (M := M) CI' ht0' (le_max_right _ _) (le_max_left _ _) hstdK'
  -- positive bonds
  obtain ⟨C1, h1, hC1, hh1, hpos1⟩ := smoSM_of_DM G K M hK hH hD
  have hposT : ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, (truncSM G M).step N ≤ h1 → ∀ n : ℤ, 0 ≤ n → n < N → 0 < (truncSM G M).bondA μ N n :=
    ⟨h1, hh1, fun μ hμ N hN n hn1 hn2 => ((hpos1 μ hμ N hN).1 n hn1 hn2).2⟩
  -- the zone of the last block
  obtain ⟨ε, hε, hJε⟩ := uniform_margin_bandHi (T := truncSM G M) hK hDT SIu.w CI.Jhi hJhi
  have hzone : ∃ e : ℝ, 0 < e ∧ ∀ μ ∈ K, ∀ t ∈ Icc (-t0') t0',
      (frozenFamily (truncSM G M) Kidx).bandHi (μ, t) - CI.softUpL.δ0 + e ≤ CI.Jhi := by
    refine ⟨ε, hε, fun μ hμ t ht => ?_⟩
    have h1 := SIu.bandHi_close μ hμ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 := SIu.window_in_chart
    have h3 := hJε μ hμ
    rw [frozen_bandHi_zero] at h1
    have := (abs_le.mp h1).2
    linarith
  have hlabels' := bulkLabels_core (T := truncSM G M) (M := M) CI' (fun ν => (PI ν).restrictSub (fun _ => hlt ν) hPsub ht0' hle0) ht0' hstd'
    hlab hposT hlt hzone
  have hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (CI.lo ν) (CI.hi ν) :=
    fun ν => bulkWindowLabels_of_le hle0 ht0' (hlabels' ν)
  let aS : Bool → Par → ℝ := (softEnds (truncSM G M) Kidx SIu.w SIl.w).1
  let bS : Bool → Par → ℝ := (softEnds (truncSM G M) Kidx SIu.w SIl.w).2
  let WS : ∀ s : Bool, WindowPhase (truncSM G M) K t0 M (aS s) (bS s) := fun s => match s with
    | true => softUpWindow (T := truncSM G M) SIu ht0 hq hlabW
    | false => softLoWindow (T := truncSM G M) SIl ht0 hq hHT hD0 hlabLo
  have hcov := windowCover_of_charts (T := truncSM G M) CI ht0.le SIu.w SIu.w_pos aS bS (fun μ => by show (frozenFamily (truncSM G M) Kidx).bandHi (μ, 0) - SIu.w = _; rw [frozen_bandHi_zero])
    (fun μ => by show (frozenFamily (truncSM G M) Kidx).bandHi (μ, 0) + SIu.w = _; rw [frozen_bandHi_zero])
    (fun μ => by show (truncSM G M).bandLo μ - SIl.w = (truncSM G M).bandLo μ - SIu.w; rw [hw])
    (fun μ => by show (truncSM G M).bandLo μ + SIl.w = (truncSM G M).bandLo μ + SIu.w; rw [hw]) hlt
    hJhi hJlo hwb
  -- the windows at `t0'' = min t0 t1` (as in `thmSmoSpec`)
  set t0'' : ℝ := min t0 t1 with ht0''def
  have ht0'' : 0 < t0'' := lt_min ht0 ht1
  have hle0'' : t0'' ≤ t0 := min_le_left _ _
  have hle1'' : t0'' ≤ t1 := min_le_right _ _
  have hP'' : paramSet K t0'' ⊆ paramSet K t0 := paramSet_mono K hle0''
  have hlabels'' : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0'' (CI.lo ν) (CI.hi ν) := by
    intro ν
    obtain ⟨Cl, h0, hh0, hl⟩ := hlabels ν
    exact ⟨Cl, h0, hh0, fun μ hμ t ht N hN htN => hl μ hμ t ⟨by linarith [ht.1], by linarith [ht.2]⟩ N hN htN⟩
  have hstd'' := hs1 t0'' ht0'' hle1''
  have hslope : ∀ ν, ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo (CI.lo ν) (CI.hi ν), deriv (fun X' => (PI ν).Sigma μ 0 X' 0) X ≤ -c := by
    intro ν
    obtain ⟨r, hr⟩ := hstd''
    exact bulk_slope ((PI ν).restrictSub (fun _ => hlt ν) hP'' ht0'' hle0'') ht0'' (fun μ hμ => ⟨hμ, ⟨by linarith, ht0''.le⟩⟩) hr
  let W : ∀ i : Fin CI.nb ⊕ Bool, WindowPhase (truncSM G M) K t0''  M (Sum.elim (fun ν _ => CI.lo ν) aS i) (Sum.elim (fun ν _ => CI.hi ν) bS i) :=
    fun i => match i with
      | Sum.inl ν => bulkPhaseWindow ((PI ν).restrictSub (fun _ => hlt ν) hP'' ht0'' hle0'') ht0'' (CI.overlap_match ν) hstd'' (hlabels'' ν) hposT (hslope ν)
      | Sum.inr s => (WS s).restrictT0 (fun μ hμ => (hcov.sub μ hμ (Sum.inr s)).2.1) ht0'' hle0''
  refine ⟨Fin CI.nb ⊕ Bool, inferInstance, Sum.elim (fun ν _ => CI.lo ν) aS, Sum.elim (fun ν _ => CI.hi ν) bS, t0'', SIu.w, W, ht0'', SIu.w_pos, hcov, ?_, ?_⟩
  · intro i μ hμ X hX hband
    rcases i with ν | s
    · exact (PI ν).Sigma_one μ hμ X hX 0 ⟨by linarith [ht0.le], ht0.le⟩
    · cases s
      · exact softLoSigma_one (C := CI.softLoL) (truncSM G M).L μ X 0
      · exact softSigma_one (C := CI.softUpL) μ X 0
  · intro hM1 i μ hμ X hX hband
    have hnh : Icc (-t0) t0 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) ht0
    rcases i with ν | s
    · filter_upwards [hnh] with t ht
      exact (PI ν).Sigma_zero μ hμ X hX t ht
    · cases s
      · have hD1 : DM (truncSM G M) K 1 := dm_mono (truncSM G M) K hM1 hK hDT
        have hX' : X ∈ Icc ((truncSM G M).bandLo μ - SIl.w) ((truncSM G M).bandLo μ + SIl.w) := by
          have := hX; simpa [aS, bS, softEnds] using this
        exact softLoSigma_zero_eventually SIl ht0 hμ hX' hband.1
          (fun t _ => frozen_arccos_integrable (truncSM G M) K Kidx hHT hD1 hμ t X)
      · have hX' : X ∈ Icc ((frozenFamily (truncSM G M) Kidx).bandHi (μ, 0) - SIu.w) ((frozenFamily (truncSM G M) Kidx).bandHi (μ, 0) + SIu.w) := by
          have := hX; simpa [aS, bS, softEnds] using this
        exact softSigma_zero_eventually SIu ht0 hμ hX' (by rw [frozen_bandHi_zero]; exact hband.2)

/-- **`ThmAi` (thm:A (i)) from the charts and the Layer-4 phase inputs.**  Everything between the chart fields and the glued coefficients is proved in `layer4_windows` (`bulkLabels_core`, `softLabels_of_chart`, `softLabelsLo_of_chart`, `softUpWindow`,
`softLoWindow`, `windowCover_of_charts`; the standing assumptions are obtained for `t0' = min t0 t1 t2` and the charts restricted to it, so there is no `hstdK`); the windows are glued by `thmAi_of_windows` and moved from `truncSM G M` to `G` by `thmAi_of_trunc`. -/
theorem thmAi_assembled (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν))
    (ht0 : 0 < t0)
    (SIu : SoftPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 M CI.softUpL)
    (SIl : SoftPhaseInputs (negFamily (frozenFamily (truncSM G M) Kidx)) (paramSet K t0) K t0 M CI.softLoL)
    (hw : SIl.w = SIu.w) (hlt : ∀ ν, CI.lo ν < CI.hi ν)
    (hJhi : ∀ μ ∈ K, (truncSM G M).bandHi μ - SIu.w < CI.Jhi)
    (hJlo : ∀ μ ∈ K, CI.Jlo < (truncSM G M).bandLo μ + SIu.w)
    (hwb : ∀ μ ∈ K, SIu.w ≤ (truncSM G M).bandHi μ - (truncSM G M).bandLo μ)
    (hKidx : Kidx = (M + 1) / 2) : ThmAi G K M := by
  intro hK hH hD
  obtain ⟨ι, hι, a, b, t0', δ, W, ht0', hδ, hcov, -, -⟩ :=
    layer4_windows (G := G) (K := K) (M := M) ⟨Kidx, t0, U, V, cPC, CPC, CI, PI, ht0, SIu, SIl, hw, hlt, hJhi, hJlo, hwb, hKidx⟩ hK hH hD
  obtain ⟨δ', Cn, C, hM, S, hδ', hsm, hact, hrule⟩ := thmAi_of_windows W ht0' hδ hcov hK (hypOn_truncSM G K M hH) (dm_truncSM G K M hD)
  obtain ⟨hM', C', hsm', hact', hrule'⟩ := thmAi_of_trunc G K M hK hH hD S δ' Cn hM C hδ' hsm hact hrule
  exact ⟨δ', Cn, C', hM', S, hδ', hsm', hact', hrule'⟩

/-- **Theorem A (i) and (ii)** with the reduced premise list of `thmAi_assembled` for `ThmAi`; `ThmAii` is `thmAii_proved` (no premises). -/
theorem thmA_of_layer4 (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CItr : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CItr.lo ν) (CItr.hi ν) M U V (CItr.bulkL ν) (CItr.bulkR ν))
    (ht0 : 0 < t0)
    (SIu : SoftPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 M CItr.softUpL)
    (SIl : SoftPhaseInputs (negFamily (frozenFamily (truncSM G M) Kidx)) (paramSet K t0) K t0 M CItr.softLoL)
    (hw : SIl.w = SIu.w) (hlt : ∀ ν, CItr.lo ν < CItr.hi ν)
    (hJhi : ∀ μ ∈ K, (truncSM G M).bandHi μ - SIu.w < CItr.Jhi)
    (hJlo : ∀ μ ∈ K, CItr.Jlo < (truncSM G M).bandLo μ + SIu.w)
    (hwb : ∀ μ ∈ K, SIu.w ≤ (truncSM G M).bandHi μ - (truncSM G M).bandLo μ)
    (hKidx : Kidx = (M + 1) / 2) (m Kidx' : ℕ) (t0' : ℝ) (CI : ChartInputs G K Kidx' t0' m (2 * Kidx') U V cPC CPC) :
    ThmAi G K M ∧ ThmAii G K m Kidx' t0' U V cPC CPC CI :=
  ⟨thmAi_assembled G K M Kidx t0 U V cPC CPC CItr PI ht0 SIu SIl hw hlt hJhi hJlo hwb hKidx, thmAii_proved CI⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.layer4_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.layer4_windows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAi_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAi_assembled

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmA_of_layer4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmA_of_layer4

end FormalResearch.JacobiEigenvectors.TheoremA

end
