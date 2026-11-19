module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.ThmA
public import FormalResearch.JacobiEigenvectors.Assembly.SoftLabels
public import FormalResearch.JacobiEigenvectors.Assembly.WindowCoverProof

/-!
# Paper J: thm:A (i) assembled from the Layer-4 inputs (L2.C9, items 1, 3, 4)

Source: Paper J `thmA.tex`, proof of `thm:A (i)` ("Location and labels", "Bulk phases", "Gluing"); frozen statement `ThmAi` (`TheoremA/Statements.lean`).

## Proved here (axiom-pinned)

* `thmAi_assembled`: `ThmAi G K M` from the chart data `CI` of `truncFamily G M` and the following premises only.
  * `PI`: the bulk phase inputs of every block (Layer 4, `BulkPhaseInputs`: Weber charts and the phase `Sigma` with its regularity and zero data);
  * `SIu`, `SIl`: the soft phase inputs of the two band ends (`SoftPhaseInputs`, Layer 4), with one common half-width `hw : SIl.w = SIu.w`;
  * `ht0 : 0 < t0` and `hstdK` (the standing assumption of the frozen family at index `Kidx`, the paper's "`t_0` small"; `stdAssump_trunc` supplies it for `min t0 t1`);
  * the geometric relations of the cover (`hlt`, `hJhi`, `hJlo`, `hwb`: blocks of positive length, the soft windows reach into the bulk range, `w <= X_s^+ - X_s^-`);
  * `hlabels : BulkWindowLabels` (see below).
  `SoftLabels`, `SoftLabelsLo` (`SoftLabels.lean`), the soft windows `WS` (`softUpWindow`, `softLoWindow`) and `hcov` (`WindowCoverProof.lean`) are **no longer premises**.
* `thmA_of_layer4`: `ThmAi /\ ThmAii` (with `thmAii_proved`) for charts `CItr` (of `truncFamily G M`) and `CI` (of `G` at order `m`).

## The remaining premise `hlabels` and the paper's chain for it

`BulkWindowLabels` says: for `t` in `(0, h_0]` the eigenvalue of `A_N(mu, t)` in the bulk window `nu` (the one `bulk_zero_window` isolates) carries the index `k' = k`.  The paper's argument
("Location and labels"):
1. Step 0 (`stepZero`): no eigenvalue of the frozen operator exceeds `X_s^+ + C_{s0} h^2`; so the eigenvalues above the soft window 0 are exactly those counted by `propThaW2` (3).
2. Soft anchor: by `propThaW2_proved` (3), (4) at `X = X_s^+ - delta_0`, the eigenvalues in the top soft window `[X_s^+ - w, X_s^+ + w]` have labels `0, 1, 2, ...` in decreasing order; the soft slope
   (`SoftPhaseInputs.mu0_slope`, `mu0_S0`) gives them as `Sigma_i^{soft}` with the prescribed spacing.
3. Count: `bulk_count` (with `bulk_kappa_sign`, the sign of `kappa = -d_X Sigma`) shows that each bulk window contains exactly the number of eigenvalues that `Sigma` predicts, and `count_label`
   (`order_label_real`, `SoftCountOrder.lean`) converts "number of eigenvalues above `x`" into "label".
4. Downward induction over a chain of windows (a Lebesgue number of the open cover `W_nu`, `windowCover_of_charts`): adjacent windows overlap in a positive-length interval, so the label of the
   eigenvalue in the overlap is the same computed from either side; the induction starts at the soft window 0, where the label is `propThaW2` (3).
5. A quantitative slope at `t = h` (from `bulk_slope` at `t = 0` and the `Sigma_bdd` bound on `d_t d_X Sigma`) makes the count of step 3 uniform in `t in (0, h_0]`.

## Not formalised

Steps 2--5 above (about 450--800 lines of Lean; steps 1 and the pieces of 3 are in the repository); the Layer-4 inputs `PI`, `SIu`, `SIl` and the Layer-1 inputs behind the chart fields.  Only `t = (frozen).step N`
is used from `BulkWindowLabels` (inside `bulkPhaseWindow`), so the statement could be narrowed to that case.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

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

/-- **`ThmAi` (thm:A (i)) from the charts and the Layer-4 phase inputs.**  Everything between the chart fields and `thmSmoSpec`'s premises `WS`, `hcov` is proved here
(`softLabels_of_chart`, `softLabelsLo_of_chart`, `softUpWindow`, `softLoWindow`, `windowCover_of_charts`); `hlabels` stays a premise. -/
theorem thmAi_assembled (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν))
    (ht0 : 0 < t0)
    (hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (CI.lo ν) (CI.hi ν))
    (hstdK : ∃ r, StdAssump (frozenFamily (truncSM G M) Kidx) (paramSet K t0) Kidx r)
    (SIu : SoftPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 M CI.softUpL)
    (SIl : SoftPhaseInputs (negFamily (frozenFamily (truncSM G M) Kidx)) (paramSet K t0) K t0 M CI.softLoL)
    (hw : SIl.w = SIu.w) (hlt : ∀ ν, CI.lo ν < CI.hi ν)
    (hJhi : ∀ μ ∈ K, (truncSM G M).bandHi μ - SIu.w < CI.Jhi) (hJlo : ∀ μ ∈ K, CI.Jlo < (truncSM G M).bandLo μ + SIu.w)
    (hwb : ∀ μ ∈ K, SIu.w ≤ (truncSM G M).bandHi μ - (truncSM G M).bandLo μ)
    (hKidx : Kidx = (M + 1) / 2) : ThmAi G K M := by
  intro hK hH hD
  have hHT := hypOn_truncSM G K M hH
  have hDT := dm_truncSM G K M hD
  have hD0 : DM (truncSM G M) K 0 := dm_zero_of_dm _ K M hK hDT
  have hq : M ≤ 2 * Kidx := by omega
  have hlab := softLabels_of_chart (T := truncSM G M) (M := M) CI ht0 (le_max_right _ _) (le_max_left _ _) hstdK
  have hlabLo := softLabelsLo_of_chart (T := truncSM G M) (M := M) CI ht0 (le_max_right _ _) (le_max_left _ _) hstdK
  let aS : Bool → Par → ℝ := (softEnds (truncSM G M) Kidx SIu.w SIl.w).1
  let bS : Bool → Par → ℝ := (softEnds (truncSM G M) Kidx SIu.w SIl.w).2
  let WS : ∀ s : Bool, WindowPhase (truncSM G M) K t0 M (aS s) (bS s) := fun s => match s with
    | true => softUpWindow (T := truncSM G M) SIu ht0 hq hlab
    | false => softLoWindow (T := truncSM G M) SIl ht0 hq hHT hD0 hlabLo
  have hcov := windowCover_of_charts (T := truncSM G M) CI ht0.le SIu.w SIu.w_pos aS bS (fun μ => by show (frozenFamily (truncSM G M) Kidx).bandHi (μ, 0) - SIu.w = _; rw [frozen_bandHi_zero])
    (fun μ => by show (frozenFamily (truncSM G M) Kidx).bandHi (μ, 0) + SIu.w = _; rw [frozen_bandHi_zero])
    (fun μ => by show (truncSM G M).bandLo μ - SIl.w = (truncSM G M).bandLo μ - SIu.w; rw [hw])
    (fun μ => by show (truncSM G M).bandLo μ + SIl.w = (truncSM G M).bandLo μ + SIu.w; rw [hw]) hlt hJhi hJlo hwb
  exact (thmSmoSpec G K M Kidx t0 U V cPC CPC CI PI ht0 hlabels aS bS WS SIu.w SIu.w_pos hcov hK hH hD hKidx).1 hK hH hD

/-- **Theorem A (i) and (ii)** with the reduced premise list of `thmAi_assembled` for `ThmAi`; `ThmAii` is `thmAii_proved` (no premises). -/
theorem thmA_of_layer4 (G : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CItr : ChartInputs (truncFamily G M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily G M) Kidx) (paramSet K t0) K t0 (CItr.lo ν) (CItr.hi ν) M U V (CItr.bulkL ν) (CItr.bulkR ν))
    (ht0 : 0 < t0)
    (hlabels : ∀ ν, BulkWindowLabels (frozenFamily (truncSM G M) Kidx) K t0 (CItr.lo ν) (CItr.hi ν))
    (hstdK : ∃ r, StdAssump (frozenFamily (truncSM G M) Kidx) (paramSet K t0) Kidx r)
    (SIu : SoftPhaseInputs (frozenFamily (truncSM G M) Kidx) (paramSet K t0) K t0 M CItr.softUpL)
    (SIl : SoftPhaseInputs (negFamily (frozenFamily (truncSM G M) Kidx)) (paramSet K t0) K t0 M CItr.softLoL)
    (hw : SIl.w = SIu.w) (hlt : ∀ ν, CItr.lo ν < CItr.hi ν)
    (hJhi : ∀ μ ∈ K, (truncSM G M).bandHi μ - SIu.w < CItr.Jhi) (hJlo : ∀ μ ∈ K, CItr.Jlo < (truncSM G M).bandLo μ + SIu.w)
    (hwb : ∀ μ ∈ K, SIu.w ≤ (truncSM G M).bandHi μ - (truncSM G M).bandLo μ)
    (hKidx : Kidx = (M + 1) / 2) (m Kidx' : ℕ) (t0' : ℝ) (CI : ChartInputs G K Kidx' t0' m (2 * Kidx') U V cPC CPC) :
    ThmAi G K M ∧ ThmAii G K m Kidx' t0' U V cPC CPC CI :=
  ⟨thmAi_assembled G K M Kidx t0 U V cPC CPC CItr PI ht0 hlabels hstdK SIu SIl hw hlt hJhi hJlo hwb hKidx, thmAii_proved CI⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAi_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAi_assembled

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmA_of_layer4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmA_of_layer4

end FormalResearch.JacobiEigenvectors.TheoremA

end
