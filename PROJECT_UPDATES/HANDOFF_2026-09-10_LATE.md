# Formal research handoff — 2026-09-10 late

This supersedes the restart/status portions of `PROJECT_UPDATES/HANDOFF_2026-09-10.md` and earlier handoffs. The Lean frontier moved materially again: the T48 zero-sector certificate, the source-current E6/A2 linear guard, the QI-A T07 finite code-dimension converse layer, and the T48 harmonic-block algebra are all now merged into the maintained reasoner branch.

## Current authoritative heads

Research/manuscript/certificate authority:

- repository: `cmbant/QIprojects:main`
- current live head: `1835b62a5ea6577c0ca685101276419cab04e671`

Lean authority:

- repository: `cmbant/reasoner:formal-research-lean`
- current maintained head after reasoner PR #23: `9f236abcb8903cfaeb5d0122387c6ddb022f9046`

Re-audit both live heads before starting new work.

## Source drift since the last Lean audit

The T07/T48 implementation work was originally audited at QIprojects `6080f36ddd7a3c85015416b793e0562caf685e5a`. Current `main` is `1835b62a...`, 23 commits later.

The `6080f36... -> 1835b62...` file delta contains:

- new QI-A T39 operational-fingerprint source/certificate files;
- new Weyl/T27 material and task-index reconciliation;
- historical QI-B data/devcontainer changes;
- **no changes to the T07 source note/script used by PR #22**;
- **no changes to the T48 source note/script used by PRs #20 and #23**;
- **no QI-C file changes**.

Therefore the T07 and T48 source matches below remain current through `1835b62...`, and the earlier QI-C Endpoint14 audit remains valid.

## Newly merged reasoner frontier

### PR #20 — T48 Spin(8) zero-sector boundary

Merged at:

`a9f670ed37d9dc54eb4b96362fb03bfcbf48c04e`.

Exact promoted Lean-content head:

`46aa00dbb7b76c74a4204eb1d6f35d7a79aef0e1`.

Aggregate run:

`34441876733`.

Lean reuses the exact 192-element `W(D4)` model and checks the source-to-standard basis change, four zero-sector facet normals, `Tr(F_aa)=1/3`, D4 support `2/3`, active counts `24,20,16,14`, and the sharp boundary value `1/3+2/3=1`.

Scope remains finite zero-sector only. It does not prove interior compact-E6 simultaneous Weyl convexity.

### PR #21 — E6/A2 source-current linear guard

Merged at:

`cc2588ab12045d225b93e364484e8251cc7d092e`.

Exact Lean-content head:

`0468a2ee1ee8402b52935d32ec599ce4ffd3a894`.

Aggregate run:

`34444000316`.

This reconciles `E6A2PhaseEnvelopeQuartic.lean` with the strengthened source verifier: the linear/sign guard `d>=|a|` is now represented and the degenerate/nondegenerate regressions showing quartic positivity alone is insufficient are formalized.

The analytic one-phase maximization and genuine compact-F4 endpoint positivity remain external.

### PR #22 — QI-A T07 finite code-dimension bounds

Merged at:

`1b3b95a30a0fbba39d25e02849b50a9762a5aa2c`.

Module:

`FormalResearch/QIA/SectorLabelOnlyCodeDimension.lean`.

Exact promoted Lean tree:

`ed773873152e4d60f690f665ed14bdbdfaef77f1`.

Exact module blob:

`d416fe01e1c34eb6de824dd2bfb2360f27e336ae`.

Exact `FormalResearch.lean` blob at validation:

`fd7956089fba6ae5c1f3678d119daebe6a9d1c2d`.

Promotion run:

`34445813054`.

That run passed placeholder rejection, `lake build FormalResearch.QIA.SectorLabelOnlyCodeDimension`, and full `lake build FormalResearch`.

Lean now proves the exact finite PSD/POVM guessing layer:

- total identifying score at most memory dimension `q`;
- uniform average success at most `q/N`;
- conditional deficiency consequence `delta >= 1-eta-q/N` from explicit ideal-success/TV premises;
- free-sector-label weighted success at most `q * sum_lambda ell(lambda) / N`, specializing to the source `q L_d/N` bound when `ell(lambda)=max_j p_j(lambda)`;
- the corresponding global deficiency consequence.

The density-state implication `omega<=I` remains an explicit hypothesis. The module does not formalize the Bergman/packing asymptotics, orbit-fidelity lemma, Fano/mutual-information form, Gaussian/Szego critical theorem, finite critical transfer, or any unrestricted-physical converse. The source-refuted unrestricted physical block-curve converse remains refuted.

### PR #23 — T48 harmonic-block factorization

Merged at:

`9f236abcb8903cfaeb5d0122387c6ddb022f9046`.

Module:

`FormalResearch/QID/E6F4HarmonicBlockFactorization.lean`.

Exact promoted Lean tree:

`257422bb2796d8a1bae6d139a32fc53bf2153979`.

Exact module blob:

`16be62fa3115b09f64261a58e77abf0a740974f5`.

Exact aggregate-import blob:

`70f4a73100f02e3aad3be8ddd18bc931085024d2`.

Promotion run:

`34470566235`.

That run passed placeholder rejection, `lake build FormalResearch.QID.E6F4HarmonicBlockFactorization`, and full `lake build FormalResearch`.

Lean proves, abstractly for finite complex matrices representing one T48 triality sector, the exact block expansion for `Z=[K,iP]`, the source identity `B=(1/2) Z_L^* Z_R`, and positivity of the same-side Gram matrix `Z^*Z`.

This does not formalize the E6 restricted-root enumeration, identify the three `8_v,8_s,8_c` modules, make the PSD/rank outer locus exact, derive common-F4 triality compatibility, prove the T33 quartic on genuine endpoints, or prove compact-E6 simultaneous Weyl convexity.

## QI-A current source frontier

T07 is now covered at its clean finite code-dimension/guessing layer by PR #22, but not at its asymptotic or unrestricted-physical layers.

A new source result has appeared since the previous Lean plan: **T39 operational invariant fingerprint**.

Canonical files:

- `QI-A/notes/OPERATIONAL_INVARIANT_FINGERPRINT.md`;
- `QI-A/notes/T39_REPORT.md`;
- `QI-A/scripts/verify_operational_fingerprint.py`;
- `QI-A/verification/verify_operational_fingerprint.txt`.

Exact verifier blob at QIprojects `1835b62...`:

`d058c7650a6a75466eb47945c3948685d13f0533`.

T39 source certifies, among other exact finite statements:

- for the four-qubit three-copy reduced algebra `C^11 direct-sum M_3(C)`, `K=14`, `R=20`, normalized fingerprint coordinates `R-1=19`, and conjugation-odd coordinates `3`;
- exact repeated-ZYYX finite-shot thresholds;
- sparse witness term/transposition accounting;
- the all-`m` Haar second moment
  `E[f_m^2] = [3 N (N^2-64)/10240] / binom(N+5,6)` with `N=2^m`, hence
  `RMS ~ (3 sqrt(6)/16) 2^(-3m/2)` and inverse-square scale `(128/27) 8^m`.

The `O(8^m)` statement is a direct-estimation one-RMS sample scale, not a universal minimax lower bound, observable-count growth, or circuit-size claim.

No QI-A manuscript theorem changed in T39.

## QI-C current status

No QI-C files changed in the audited `6080f36... -> 1835b62...` delta. The canonical all-`m` qubit-tail verifier remains unchanged from the earlier exact blob audit `e5d44a1733ce0520bebd37a9172348b1476f7463`.

Keep Endpoint14 maintenance closed unless the QI-C source changes or Lean regresses. Existing Lean coverage is the determinant/nonvanishing/injectivity certificate chain, not automatically the full geometric local-identifiability theorem.

## QI-D T48 / T49 status after PR #23

Both theorem-sized T48 Lean candidates from the previous handoff are now closed:

1. four-facet Spin(8) zero-sector finite certificate — PR #20;
2. abstract adapted/harmonic-block algebra — PR #23.

The remaining exceptional interior is still T49 source-side research. Do not formalize a merely PSD/rank-feasible outer-locus point as a genuine compact endpoint or counterexample, and do not start a Lean “T49 completion” branch until source work proves a new exact compatibility theorem/certificate.

## QIprojects planning status

At current QIprojects `main`, `docs/lean_status.md`, `docs/agent_tasks/T20_REPORT.md`, and `docs/agent_tasks/T20_lean_small_targets.md` still reflect the older post-PR18/T48 reconciliation. They do not yet record reasoner PRs #20-#23 or the new T39 source result.

Therefore **do not reuse their old candidate order verbatim**. This handoff is the current restart authority until those planning files are reconciled. A staging branch `agents/t20-lean-reconcile-t07-t48-harmonic` exists at QIprojects head `1835b62...` but contains no planning-file changes as of this handoff; no QIprojects merge was performed in this batch.

## Recommended next-work order

Re-audit both live heads before implementation.

1. **QI-A T39 finite fingerprint/dimension certificate.** This is now the cleanest small exact target. Reuse `FormalResearch.QIA.MultiplicityProfileDimensions` and existing four-qubit `d=3` census infrastructure to source-match `C^11 direct-sum M_3(C)`, `K=14`, `R=20`, `R-1=19`, and odd dimension `3`. Keep the operational statement “complete normalized fingerprint needs `R-1` coordinates” separate unless the relevant affine/state-space argument is represented faithfully.
2. **QI-A T39 Haar second-moment certificate**, if the finite `S_6` cycle enumeration / binomial closed form can be isolated cleanly. Preserve the source boundary: the resulting `8^m` scale is not a universal sample-complexity lower bound.
3. **General type-D support/Procrustes semantic bridge**, preferably first for the specific row/column and opposite-parity sign atoms already used by `NestedUpperSupportBridge`, if current real-matrix infrastructure makes that tractable. This remains higher value but substantially larger than T39 finite arithmetic.
4. **Further T07 layers** only when their operational hypotheses can be represented faithfully; do not restore the refuted unrestricted-physical converse.
5. **T49 exceptional interior** only after a new source-proved exact compatibility theorem/certificate appears.
6. **New Weyl/QI-B results** should be audited from their theorem-local source before entering the Lean queue. Current QIprojects has new T27 q-Carron/Lewis material, but its general q-Hahn/classical-limit content is not automatically a small Lean target.

## Restart rules

1. Read this handoff first, then recheck the current `formal-research-lean` and QIprojects `main` heads.
2. Re-audit theorem-local source files if QIprojects has moved.
3. Start each Lean target from the current maintained reasoner head on a fresh `agents/<task>-<short-name>` branch.
4. Reject `sorry` / `admit`; hard-build the smallest changed module; import it from `FormalResearch.lean`; then hard-build full `FormalResearch` on the exact promoted Lean tree.
5. Record exact source pin/blob, reasoner verification head/module blob/aggregate blob, Actions run, merge commit, and external assumptions.
6. Merge only the exact tested code tree or a cleanup tree whose Lean bytes are source-identical to the tested tree.
7. If source/Lean work materially strengthens a manuscript theorem, use a separate review checkpoint rather than silently changing the paper.

## Claim discipline

Keep these states distinct: SOURCE/PAPER, exact external certificate, FORMALIZED, MODULE-GREEN, AGGREGATE-GREEN, MERGED, and full semantic theorem.

In particular:

- PR #22 is the finite T07 code-dimension/guessing layer, not the full approximate-memory theorem;
- PR #20 is a zero-sector D4/Spin(8) boundary certificate, not an interior E6 theorem;
- PR #21 makes the E6/A2 quartic layer source-current but does not supply analytic phase maximization or genuine-endpoint positivity;
- PR #23 is harmonic-block matrix algebra, not common-F4/triality compatibility;
- T39's `8^m` scale is a direct sparse-observable RMS estimation scale, not a universal lower bound;
- QI-C Endpoint14 remains a certificate chain, not automatically the full geometric theorem.
