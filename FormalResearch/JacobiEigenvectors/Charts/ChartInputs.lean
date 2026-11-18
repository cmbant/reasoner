module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.TransferCoefficients

/-!
# Paper J, charts: `ChartInputs`, the bundle of all chart / special-function hypotheses of Layers 2--3

The bundle consumed by the statements of `TheoremA/Statements.lean` and `TheoremB/Statements.lean`.  For a family `F` (parameter `mu`, compact set `K`),
the parity-freezing depth `Kidx` (so `2 Kidx = q_m`-ish) and `t0`, it contains, for the **frozen family** `frozenFamily F Kidx` on the parameter set
`K x [-t0, t0]` (the second component is the freezing parameter `t`, evaluated at `t = h` at the end, `Setting.frozenFamily_jacobiMat_at_step`):

* `pc`: `ParabolicCylinderFacts` (Layer 4: DLMF/Olver);
* `bulkL`, `bulkR`: the left / right Weber charts at order `m` on the bulk energy range `[Jlo, Jhi]` (`BulkWeberChart`; `bulkR` is a chart of the mirror family);
* `softUpL`, `softUpR`, `softLoL`, `softLoR`: the soft-edge charts at the upper edge (left and right solution) and, through the gauge `negFamily`, the lower edge;
  order `m`, shift index `q` (admissibility `2 ceil(m/2) <= q <= 2 floor(m/2) + 2` is a hypothesis of the statements, not a field: for the pair of orders `m, m+1` of
  Theorem B the *same* `q` is used and is one shift short at even `m + 1`);
* `cover`: the bulk range and the soft windows cover the band (`J = [X_s^- + delta_0, X_s^+ - delta_0]` and `|X - X_s^pm| <= delta_0`), for all `mu in K`, `|t| <= t0`.

Order `m + 1` charts (Theorem B) are a second `ChartInputs` with the same `q`; the link between the two (same ladder, parity identity `eq:thb-parity`) is `TransferInputs`.
The eigenvalue-rule inputs `BulkPhaseInputs` are separate (they live at order `max M 1`).

Not here: the hypotheses (H1)--(H3), `(D_M)` / `(E_K)` (`Setting`); those are arguments of the statements, so that the chart inputs can be reused for several symbol classes.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Setting

/-- The parameter set `K x [-t0, t0]` of the frozen family. -/
def paramSet {Par : Type*} (K : Set Par) (t0 : ℝ) : Set (Par × ℝ) := K ×ˢ Set.Icc (-t0) t0

/-- **All chart hypotheses** (see the module docstring). -/
structure ChartInputs {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) (t0 : ℝ)
    (m q : ℕ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ) where
  pc : ParabolicCylinderFacts U V cPC CPC
  Jlo : ℝ
  Jhi : ℝ
  bulkL : BulkWeberChart (frozenFamily F Kidx) (paramSet K t0) Jlo Jhi m U V
  bulkR : BulkWeberChart (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) Jlo Jhi m U V
  softUpL : SoftEdgeChart (frozenFamily F Kidx) (paramSet K t0) m q U V
  softUpR : SoftEdgeChart (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) m q U V
  softLoL : SoftEdgeChart (negFamily (frozenFamily F Kidx)) (paramSet K t0) m q U V
  softLoR : SoftEdgeChart (mirrorFamily (negFamily (frozenFamily F Kidx))) (paramSet K t0) m q U V
  /-- the bulk range lies inside the band and, with the two soft windows, covers it. -/
  cover : ∀ p ∈ paramSet K t0,
    (frozenFamily F Kidx).bandLo p < Jlo ∧ Jlo ≤ Jhi ∧ Jhi < (frozenFamily F Kidx).bandHi p ∧
    (frozenFamily F Kidx).bandHi p ≤ Jhi + softUpL.δ0 ∧ Jlo - softLoL.δ0 ≤ (frozenFamily F Kidx).bandLo p

end FormalResearch.JacobiEigenvectors.Charts
