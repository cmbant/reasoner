# Project updates and author correction notes

Snapshot date: 2026-09-04.

This directory is an author-facing correction and update ledger for the research papers and handoff archives associated with the `FormalResearch` Lean verification spine. It is **not** a substitute for the manuscripts, archive handoffs, or Lean source.

## How to use these notes

For each stable project ID, the corresponding note records only changes that an original paper/archive author should act on: newer authoritative handoffs, corrected notation or formulas, claims that can be promoted or must be weakened, newly formalized exact fragments, and remaining specification mismatches.

The trust layers are deliberately separate:

- **PAPER / ARCHIVE:** what the current handoff or manuscript states.
- **EXACT DERIVATION / AUDIT:** exact algebra or a restartable certificate outside Lean.
- **FORMALIZED-UNCOMPILED:** Lean source exists but has not passed the relevant exact-head build.
- **LEAN-CHECKED:** the exact source was imported by the branch aggregate and the relevant exact-head GitHub Actions step passed.
- **EXTERNAL:** a load-bearing analytic/geometric theorem is intentionally outside the current Lean formalization.

A green workflow by itself is not enough if the relevant aggregate/build step was allowed to continue on error. Check the exact-head job steps.

## Current notes

- `AUX-BV_2026-09-04.md` — Blaschke–Virasoro v13: quartic charge-gap correction/promotion path, corrected quartic coordinate convention, and degree-five boundary.
- `AUX-L_2026-09-04.md` — uniform flux-balanced Laguerre companion: live authority advanced to v23 on 2026-09-04; v22 progressive-path wording correction.
- `AUX-QW_2026-09-04.md` — q-Weyl / quantum-6j sequel classification and current open/checked boundary.
- `AUX-W_2026-09-04.md` — Weyl-midpoint Wigner/Racah manuscript genealogy and separation from the sequel projects.
- `LEAN_AND_GENEALOGY_2026-09-04.md` — repository head/CI discipline, branch cleanup, and stable-ID genealogy changes.

Add a new project note whenever Lean analysis exposes a paper correction, a theorem is promoted/demoted, or a newer archive changes the authoritative handoff.
