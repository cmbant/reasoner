# Lean and archive genealogy update

Date: 2026-09-04

## Branch discipline

Repository: `cmbant/reasoner`  
Working branch: `formal-research-lean`  
Default branch: intentionally untouched.

The takeover started from observed head

`108f611b46c4a6cdc7b3fea5162ae01804e26c73`

(`Import Blaschke composition energy transfer`).

### CI audit correction

The historical workflow-level `success` at that head and at the subsequent cleanup head **must not be read as a successful Lean aggregate build**. A 2026-09-04 decoded-log audit found that the workflow invoked project source files using `lake env lean ...` before project `.olean` files existed, producing `unknown module prefix 'FormalResearch'` for several steps, while `continue-on-error: true` masked those failures. The old aggregate source invocation was affected by the same import-resolution problem. The old QI-B2 Krawtchouk diagnostic also contained a genuine tactic failure under the current pinned Lean/mathlib resolution.

Therefore all earlier `LEAN-CHECKED` labels that depended only on the workflow-level green badge are **provisionally withdrawn pending re-certification under a hard Lake build**. This does not assert that the Lean theorems are mathematically false; it corrects the verification evidence.

The workflow is being repaired to use hard Lake build targets:

- `lake build FormalResearch.Blaschke.QuarticChargeGapAlgebra` for the new AUX-BV module;
- `lake build FormalResearch` for the aggregate library.

Only after those exact-head hard steps pass should imported modules be called `LEAN-CHECKED`. Direct source invocations may remain as diagnostics after the library build, but they are not the trust gate.

On 2026-09-04 two historical root Python files inherited from the repository’s original master history were confirmed unrelated to the formal-research project and removed **only from `formal-research-lean`**:

- `apis.py`
- `reasoning_agent.py`

After those deletions the branch head was

`74e7a48af59e236ca4223f57996dad4e102a0ed9`.

The later research/update commit was

`1441079ed5c17aa90ce503047010acd25548b90b`.

Any later commit must re-query the head and exact-head CI before assigning `LEAN-CHECKED`.

## CI trust rule

A workflow badge is not a proof artifact. A theorem becomes `LEAN-CHECKED` only when:

1. its exact source is in the current branch;
2. the placeholder scan passes;
3. the relevant hard Lake module/library build at that exact head succeeds;
4. the theorem-to-paper semantic audit still matches the current manuscript claim.

Compilation is not by itself a specification audit. Compare the Lean theorem statement with the current paper/archive statement after any paper correction.

## Live genealogy changes since the September-2 atlas

- `AUX-W`: current `paper3_v7_8_4_complete_handoff.zip`.
- `AUX-BV`: current `Blaschke_Virasoro_Handoff_2026-09-03_v13.zip`.
- new stable ID `AUX-QW`: current `q_weyl_turn8_handoff.zip`.
- new stable ID `AUX-L`: the family advanced again on 2026-09-04; current authority is `balanced_laguerre_uniform_pair_v23_bundle.zip`, after v22 and v21.

The old `RESEARCH_PROJECT_MAP_AND_NOTE_ATLAS_2026-09-02_REV3.md` and the repository `THEOREM_MAP.md` remain useful historical provenance, but neither should be used as a live source of truth without reconciliation against current archives/source/CI.

## Current formalization action

A new AUX-BV exact algebra module exists at

`FormalResearch/Blaschke/QuarticChargeGapAlgebra.lean`.

Its scope is intentionally narrower than the analytic theorem:

- corrected normalized quartic coordinate convention;
- exact critical-conic polynomial;
- positivity of `L_-`, `L_+` from `epsilon>=0`;
- downstream `F1/F2/F3` sign certificate;
- squared-gap factorization and Gate-A unsquaring logic.

The model-space Bessel inequality and the raw residue/metric construction of the singular values remain external inputs unless separately formalized. Do not encode those hard inputs as assumptions that merely restate the desired charge-gap conclusion.

Current verification status of this new module: `FORMALIZED-UNCOMPILED` until a repaired exact-head Lake build succeeds.
