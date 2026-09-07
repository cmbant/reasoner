# Project updates and author correction notes

Original snapshot date: 2026-09-04. Source-authority migration synchronized: 2026-09-05. Latest cross-repository handoff: **2026-09-07**.

**Current manuscript/source authority is `cmbant/QIprojects:main`.** This directory is retained as the Lean-side audit ledger and historical formalization record. Lean remains in `cmbant/reasoner`, branch `formal-research-lean`; do not copy manuscript/source authority back into this repository.

## Start here

For current status, read:

- `HANDOFF_2026-09-07.md` — current exact QIprojects/reasoner heads, Endpoint14 status, latest aggregate blockers, and the new QIprojects T20 Lean roadmap.
- `HANDOFF_2026-09-06.md` — historical Endpoint14 development record and detailed dead-end/resource notes.
- `SOURCE_SYNC_2026-09-05.md` — migration reconciliation from archive-era sources to QIprojects.

As recorded in the 2026-09-07 handoff, current QIprojects main is far ahead of the original migration pin. Always fetch live `QIprojects/main` before relying on this directory.

## Trust layers

- **PAPER / SOURCE:** what current QIprojects source/status states.
- **EXACT DERIVATION / AUDIT:** exact algebra or a restartable certificate outside Lean.
- **FORMALIZED:** Lean source exists.
- **MODULE-GREEN:** the exact Lean module build passed at the stated head.
- **AGGREGATE-GREEN:** `lake build FormalResearch` passed at the stated head.
- **LEAN-CHECKED:** semantic source match plus the required successful exact-head Lean gates under the current project discipline.
- **EXTERNAL:** a load-bearing analytic/geometric/special-function input is intentionally outside the current Lean formalization.

A green workflow badge alone is never sufficient if relevant proof steps were diagnostic-only, masked, stale, or semantically mismatched.

## Current QIprojects navigation

Useful current source-side entry points include:

- `AGENTS.md` — source layout and Lean cross-repository rules;
- `QI-A/notes/EXTENSION_PROJECTS.md` — current cross-QI theorem/extension priorities;
- `QI-B/HANDOFF_2026-09-06.md` and `QI-B/B4-orbit-bergman/README_HANDOFF.md` — active B4 complex-orbit program and open flagship inequality;
- `QI-B/B2-hamming/HANDOFF_MANIFEST.md` — canonical Hamming source layout;
- `QI-C/code/verify_qubit_ci_tail_proof.py` — canonical Endpoint14/all-n qubit-tail semantic certificate;
- `Blaschke/HANDOFF.md` — current v13 target-free/Van-Vleck/transvectant direction and claim status;
- `docs/agent_tasks/T20_lean_small_targets.md` — five small post-Endpoint Lean targets;
- `QI-D/notes/operator_kostant/DS_STRICTLY_CONTAINS_CONV_D4.md` — exact-rational D4 strengthening certificate;
- `ResearchNotes/README.md` — standalone new Weyl T2 and antiunitary-odd-invariant notes.

Do **not** assume `QIprojects/docs/lean_status.md` is current on main: as of the 2026-09-07 audit it is not present on main, and the old copy exists only on a stale formalization branch. Likewise `QIprojects/docs/reasoner_head.txt` is an audit snapshot, not the live reasoner head.

## Historical Lean-side notes

- `AUX-BV_2026-09-04.md` — original Blaschke v13 audit; use current `QIprojects/Blaschke/HANDOFF.md` for live source status.
- `AUX-L_2026-09-04.md` — archive-era Laguerre classification; current related research notes live in QIprojects.
- `AUX-QW_2026-09-04.md` — archive-era q-Weyl classification; current q-Weyl/Weyl-T2 source has advanced substantially.
- `AUX-W_2026-09-04.md` — archive-era Weyl/P3 genealogy.
- `LEAN_AND_GENEALOGY_2026-09-04.md` — historical trust/CI audit; superseded for current heads/status by `HANDOFF_2026-09-07.md`.
