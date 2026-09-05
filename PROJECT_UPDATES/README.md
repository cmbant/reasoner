# Project updates and author correction notes

Original snapshot date: 2026-09-04. Source-authority migration synchronized: 2026-09-05.

**Current manuscript/source authority is now `cmbant/QIprojects`.** This directory is retained as the Lean-side audit ledger and historical formalization record. Project-local author corrections should be read from the corresponding QIprojects `AUTHOR_UPDATE_YYYY-MM-DD.md` file when one exists.

The Lean repository remains `cmbant/reasoner`, branch `formal-research-lean`; do not copy manuscript/source authority back into this repository. Exact source matching should now cite a QIprojects path/commit.

## Trust layers

- **PAPER / SOURCE:** what the current QIprojects source/status states.
- **EXACT DERIVATION / AUDIT:** exact algebra or a restartable certificate outside Lean.
- **FORMALIZED:** Lean source exists.
- **MODULE-GREEN:** the exact Lean module build passed at the stated head.
- **AGGREGATE-GREEN:** `lake build FormalResearch` passed at the stated head.
- **LEAN-CHECKED:** semantic source match plus the relevant successful exact-head Lean build(s), with no masked failures/placeholders.
- **EXTERNAL:** a load-bearing analytic/geometric/special-function input is intentionally outside the current Lean formalization.

A green workflow by itself is not enough if relevant proof steps were diagnostic-only or allowed to fail.

## Current source-side notes

In `cmbant/QIprojects`:

- `Blaschke/AUTHOR_UPDATE_2026-09-05.md`
- `Weyl/P3/AUTHOR_UPDATE_2026-09-05.md`
- `Weyl/q-Weyl/AUTHOR_UPDATE_2026-09-05.md`
- `ResearchNotes/Weyl/AUTHOR_UPDATE_2026-09-05.md`
- `QI-C/AUTHOR_UPDATE_2026-09-05.md`
- `docs/lean_status.md`

## Historical Lean-side notes

- `AUX-BV_2026-09-04.md` — original Blaschke v13 audit; superseded for source paths/status navigation by the QIprojects Blaschke author update.
- `AUX-L_2026-09-04.md` — archive-era Laguerre classification; superseded by QIprojects' ResearchNotes classification.
- `AUX-QW_2026-09-04.md` — original q-Weyl classification; current source is `QIprojects/Weyl/q-Weyl` turn 8.
- `AUX-W_2026-09-04.md` — archive-era Weyl/P3 genealogy; current source is QIprojects Paper III v7.9.0.
- `LEAN_AND_GENEALOGY_2026-09-04.md` — historical trust/CI audit; current cross-repository status is QIprojects `docs/lean_status.md`.

See `SOURCE_SYNC_2026-09-05.md` for the exact migration reconciliation.
