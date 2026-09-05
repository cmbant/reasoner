# Source migration sync — QIprojects

Date: 2026-09-05

The research source corpus has moved to `cmbant/QIprojects`. From this point forward:

- manuscript/source/provenance authority is QIprojects;
- Lean remains in `cmbant/reasoner:formal-research-lean`;
- Library ZIP names/file IDs are historical ingest provenance, not the live source selector;
- semantic formalization checks should cite an exact QIprojects path/commit.

## Reconciled current sources

- **Weyl/P3:** QIprojects current source is Paper III **v7.9.0**, provenance archive `paper3_v7_9_0_complete_handoff.zip`, main `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`. The old v7.8.4 Lean-side update is genealogy only.
- **q-Weyl:** QIprojects `Weyl/q-Weyl`, cumulative turn-8 handoff. Candidate global C2/six-edge claims remain mixed proof/evidence and are not dedicated-Lean-checked.
- **Balanced Laguerre:** current repository classification is `ResearchNotes/Weyl/all_ratios_laguerre_balanced_pair.md`; v23 material is preserved under `ResearchNotes/Weyl/history/uniform_laguerre_balanced_pair/`. Do not retain `AUX-L` as a live project identity from archive filenames alone.
- **Blaschke:** QIprojects `Blaschke/`, v13 provenance. Canonical paper source is `Blaschke/tex/paper/blaschke_virasoro.tex`. The quartic `U=(Re s)^2` coordinate issue is recorded in the project-local author update.
- **QI-C:** QIprojects `QI-C/`; the semantic Endpoint14 determinant certificate is `QI-C/code/verify_qubit_ci_tail_proof.py` with the fixed 14x14 minor and exact factorization.

## Lean status at migration reconciliation

Before this documentation-only sync commit, the formalization head was `188cd8e255afb6091d455b35439734392f62b80d`.

At that head, the compact ordinary frontier passed all listed module checks and placeholder rejection. The separate `FormalResearch.QIC.Endpoint14Evaluation` job timed out after 900 seconds with exit 124 and no Lean theorem/type error. The full aggregate was not re-certified.

The next QI-C task is to replace the expensive repeated native determinant evaluation with a single exact symbolic determinant certificate matching QIprojects' fixed minor, preferably using the pinned mathlib Bird/`eval_det` machinery or another polynomial-time exact determinant certificate.

## Author notes now live with the source

The current author-facing correction notes are maintained in QIprojects, not here. This directory remains useful as a historical Lean audit trail only.
