module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftWindowProof
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkConj1
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyBulk
public import FormalResearch.JacobiEigenvectors.TheoremB.TwoOrdersBulk
public import FormalResearch.JacobiEigenvectors.Assembly.ChartRestrict

/-!
# Paper J: assembly of Theorem A (ii) (L2.C9, findings F-BB-4, F-BB-5, F-t0)

Source: Paper J `thmA.tex`, proof of `thm:A (ii)` and "The relative statement"; frozen statements `ThmAi`, `ThmAii`, `ThmSmoSpec` (`TheoremA/Statements.lean`).  This module imports both `TheoremA` and `TheoremB`
(`bulk_env_sq_sum` is in `TheoremB/TwoOrdersBulk.lean`).

## Proved here (axiom-pinned)

* `bulkEnvSum_of_stdAssump`: **F-BB-4 resolved by `TheoremB.bulk_env_sq_sum`** (no change to `PropThaW`): the bulk envelope sum `sum_n bulkEnv^2 <= C`.
* `thmAii_of_std`: `ThmAii` from the standing assumptions of the frozen family on `paramSet K t0` at indices `m/2` and `Kidx`: `thmAii_of_propThaW` with `propThaW` (proved, `BulkConj1.lean`), `propThaW2_proved`, `bulkEnvSum_of_stdAssump`,
  `softWindowT_of_chart` (**F-BB-5 resolved**, `TheoremA/SoftWindowProof.lean`) and `spectrumCovered`.
* `thmAii_of_restrict`, `thmAii_proved`: **`ThmAii` (thm:A (ii)) proved for every chart data `CI`**, no premise beyond those of `ThmAii` (compact `K`, `(H1)`--`(H3)`, `(D_{2 Kidx + 1})`): the standing assumptions are obtained for
  `t0' = min t0 t1` from `stdAssump_frozen_all` (`FrozenStandard`) and the charts are restricted to it by `ChartInputs.restrict` (`Assembly/ChartRestrict.lean`, **F-t0 resolved**); the statement for `t0'` gives that for `t0`
  (`h <= min h_m t0'`; vacuous if `t0 <= 0`).
* `thmA_assembled`: `ThmAi G K M /\ ThmAii G K m Kidx' t0' .. CI`.  The two parts live on different chart data (`ThmAi`: `truncFamily G M` at order `max M 1`; `ThmAii`: `G` at order `m`), so the wrapper takes both.
  `ThmAii` needs nothing more; `ThmAi` is `thmSmoSpec` (existence part) under its named premises: the bulk phase inputs `PI`, `hlabels` (labels = indices in the bulk windows), the window phases `WS`
  with their cover `hcov`, `0 < t0` (all of `thmSmoSpec`).
  The reduced premise list (`PI`, `SoftPhaseInputs` and the geometric relations of the cover only: `hlabels`, `WS`, `hcov` and the standing assumptions are proved) is `thmA_of_layer4` in `Assembly/ThmAi.lean`.

## Differences from the paper

* `ThmAii` does not need `0 < t0` (vacuous otherwise).  The paper's "`t_0` small" is the restriction `ChartInputs.restrict`.

## Not formalised

The Layer-1 inputs behind the chart hypotheses (`ChartInputs` fields, including `zeta_T`); for `ThmAi` the premises of `thmSmoSpec` listed above.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

section Asm

variable {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **F-BB-4 resolved**: `BulkEnvSum` is `TheoremB.bulk_env_sq_sum` for every block (`1 <= m`, the mirror overlap `overlap_match`, `StdAssump` at index `m/2`). -/
theorem bulkEnvSum_of_stdAssump (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdM : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r) : BulkEnvSum CI := by
  obtain ⟨r, hr⟩ := hstdM
  intro ν
  obtain ⟨CS, h1, hh1, H⟩ := TheoremB.bulk_env_sq_sum (CI.bulkL ν) (CI.bulkR ν) hm (CI.overlap_match ν) r hr
  refine ⟨CS, h1, hh1, fun μ hμ X hX N hN hst hst' => ?_⟩
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  exact H (μ, F.step N) ⟨hμ, ⟨by linarith, hst'⟩⟩ X hX N hN hst

/-- **`ThmAii` from the standing assumptions of the frozen family on `paramSet K t0`**: `propThaW` (proved), `propThaW2_proved`, `bulkEnvSum_of_stdAssump`, `softWindowT_of_chart` and `spectrumCovered`
(through `thmAii_of_propThaW`). -/
theorem thmAii_of_std (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC)
    (hstdM : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) :
    ThmAii F K m Kidx t0 U V cPC CPC CI := by
  intro hm1 hKidx hK hH hD
  have hD1 : DM F K 1 := dm_mono F K (by omega : 1 ≤ 2 * ((m + 1) / 2) + 1) hK hD
  exact thmAii_of_propThaW CI hstdM hstdK (bulkEnvSum_of_stdAssump CI hm1 hstdM) (softWindowT_of_chart hK hD1 CI)
    (fun ν => propThaW (CI.bulkL ν) (CI.bulkR ν)) hm1 hKidx hK hH hD

/-- `ThmAii` for the restricted charts (`t0' <= t0`) gives `ThmAii` for the original ones (`h <= min h_m t0'`). -/
theorem thmAii_of_restrict (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) {t0' : ℝ} (ht : 0 < t0') (hle : t0' ≤ t0)
    (H : ThmAii F K m Kidx t0' U V cPC CPC (CI.restrict hle)) : ThmAii F K m Kidx t0 U V cPC CPC CI := by
  intro hm hKidx hK hH hD
  obtain ⟨⟨C, hm1, hmp, Hc⟩, Hr⟩ := H hm hKidx hK hH hD
  refine ⟨⟨C, min hm1 t0', lt_min hmp ht, fun μ hμ N hN hNt X Um hE k => ?_⟩, fun ε hε => ?_⟩
  · exact Hc μ hμ N (hN.trans (min_le_left _ _)) (hN.trans (min_le_right _ _)) X Um hE k
  · obtain ⟨Cε, hε', hεp, Hε⟩ := Hr ε hε
    refine ⟨Cε, min hε' t0', lt_min hεp ht, fun μ hμ N hN hNt X Um hE k n hn hT => ?_⟩
    exact Hε μ hμ N (hN.trans (min_le_left _ _)) (hN.trans (min_le_right _ _)) X Um hE k n hn hT

/-- **`ThmAii` (thm:A (ii)), proved**: for every chart data `CI` (no further premises than those of `ThmAii`: compact `K`, `(H1)`--`(H3)`, `(D_{2 Kidx+1})`).  The standing assumptions of the frozen family
(`FrozenStandard`, `stdAssump_frozen_all`) are obtained for `t0' = min t0 t1` and the chart data are restricted to it (`ChartInputs.restrict`, finding F-t0).  If `t0 <= 0` the statement is vacuous
(`h = step N > 0`). -/
theorem thmAii_proved (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) : ThmAii F K m Kidx t0 U V cPC CPC CI := by
  intro hm hKidx hK hH hD
  by_cases ht0 : 0 < t0
  · have hDc : DM F K (2 * Kidx + 1) := by rw [hKidx]; exact hD
    obtain ⟨t1, ht1, r, hr⟩ := TheoremB.stdAssump_frozen_all F K Kidx hK hH hDc
    have ht' : 0 < min t0 t1 := lt_min ht0 ht1
    have hle : min t0 t1 ≤ t0 := min_le_left _ _
    have H := thmAii_of_std (CI.restrict hle) ⟨r, hr _ ht' (min_le_right _ _) (m / 2) (by omega)⟩
      ⟨r, hr _ ht' (min_le_right _ _) Kidx le_rfl⟩
    exact thmAii_of_restrict CI ht' hle H hm hKidx hK hH hD
  · refine ⟨⟨0, 1, one_pos, fun μ hμ N hN hNt => ?_⟩, fun ε hε => ⟨0, 1, one_pos, fun μ hμ N hN hNt => ?_⟩⟩
    · exact absurd hNt (not_le.mpr (lt_of_le_of_lt (not_lt.mp ht0) (FormalResearch.JB.stepSize_pos F.L_pos N)))
    · exact absurd hNt (not_le.mpr (lt_of_le_of_lt (not_lt.mp ht0) (FormalResearch.JB.stepSize_pos F.L_pos N)))

end Asm

/-- **Theorem A (i) and (ii)** for the families `G` (truncated at order `M`, charts `CItr`) and `G` with charts `CI` at order `m`: `ThmAi` is `thmSmoSpec` (existence part) under its named premises (`PI`, `hlabels`, `WS`, `hcov`,
the window data of the band), `ThmAii` is `thmAii_proved` (no premises). -/
theorem thmA_assembled (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CItr : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CItr.lo ν) (CItr.hi ν) M U V (CItr.bulkL ν) (CItr.bulkR ν))
    (ht0 : 0 < t0)
    (hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (CItr.lo ν) (CItr.hi ν))
    (aS bS : Bool → Par → ℝ) (WS : ∀ s : Bool, WindowPhase (truncSM G M) K t0 M (aS s) (bS s))
    (δ : ℝ) (hδ : 0 < δ)
    (hcov : WindowCover (truncSM G M) K (Sum.elim (fun ν _ => CItr.lo ν) aS) (Sum.elim (fun ν _ => CItr.hi ν) bS) δ)
    (hKidx : Kidx = (M + 1) / 2) (m Kidx' : ℕ) (t0' : ℝ) (CI : ChartInputs G K Kidx' t0' m (2 * Kidx') U V cPC CPC) :
    ThmAi G K M ∧ ThmAii G K m Kidx' t0' U V cPC CPC CI := by
  refine ⟨?_, thmAii_proved CI⟩
  intro hK hH hD
  exact (thmSmoSpec G K M Kidx t0 U V cPC CPC CItr PI ht0 hlabels aS bS WS δ hδ hcov hK hH hD hKidx).1 hK hH hD

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAii_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAii_proved

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkEnvSum_of_stdAssump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkEnvSum_of_stdAssump

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmA_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmA_assembled

end FormalResearch.JacobiEigenvectors.TheoremA

end
