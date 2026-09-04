# Lean and archive genealogy update

Date: 2026-09-04

## Branch discipline

Repository: `cmbant/reasoner`  
Working branch: `formal-research-lean`  
Default branch: intentionally untouched.

The takeover started from exact observed head

`108f611b46c4a6cdc7b3fea5162ae01804e26c73`

(`Import Blaschke composition energy transfer`). Its exact-head `Lean frontier diagnostics` run had a successful aggregate import.

On 2026-09-04 two historical root Python files inherited from the repository’s original master history were confirmed unrelated to the formal-research project and removed **only from `formal-research-lean`**:

- `apis.py`
- `reasoning_agent.py`

After those deletions the branch head was

`74e7a48af59e236ca4223f57996dad4e102a0ed9`.

Any later commit should re-query the head and exact-head CI before assigning `LEAN-CHECKED`.

## CI trust rule

The workflow uses `continue-on-error` for diagnostic compile steps, including the aggregate import. Therefore workflow-level green is not sufficient by itself. Inspect the exact job step `Aggregate import` (and any dedicated module step) at the exact head. A theorem becomes `LEAN-CHECKED` only when its exact imported source has actually compiled and the placeholder scan passes.

Compilation is still not specification verification. Compare the Lean theorem statement with the current paper/archive statement after any paper correction.

## Live genealogy changes since the September-2 atlas

- `AUX-W`: current `paper3_v7_8_4_complete_handoff.zip`.
- `AUX-BV`: current `Blaschke_Virasoro_Handoff_2026-09-03_v13.zip`.
- new stable ID `AUX-QW`: current `q_weyl_turn8_handoff.zip`.
- new stable ID `AUX-L`: the family advanced again on 2026-09-04; current authority is `balanced_laguerre_uniform_pair_v23_bundle.zip`, after v22 and v21.

The old `RESEARCH_PROJECT_MAP_AND_NOTE_ATLAS_2026-09-02_REV3.md` and the repository `THEOREM_MAP.md` remain useful historical provenance, but neither should be used as a live source of truth without reconciliation against current archives/source/CI.

## Current formalization action

A new AUX-BV exact algebra module is being added at

`FormalResearch/Blaschke/QuarticChargeGapAlgebra.lean`.

Its scope is intentionally narrower than the analytic theorem:

- corrected normalized quartic coordinate convention;
- exact critical-conic polynomial;
- positivity of `L_-`, `L_+` from `epsilon>=0`;
- downstream `F1/F2/F3` sign certificate;
- squared-gap factorization and Gate-A unsquaring logic.

The model-space Bessel inequality and the raw residue/metric construction of the singular values remain external inputs unless separately formalized. Do not encode those hard inputs as assumptions that merely restate the desired charge-gap conclusion.
