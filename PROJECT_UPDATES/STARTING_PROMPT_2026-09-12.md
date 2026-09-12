# Updated starting prompt — 2026-09-12

Use the following prompt to start the next agent/session.

---

Continue the QI-A Lean formalization directly in the linked GitHub repositories. Do repository work, not analysis-only discussion, and proceed autonomously through small source-faithful PRs unless genuinely blocked.

First read `PROJECT_UPDATES/HANDOFF_2026-09-12_0620.md` from `cmbant/reasoner` branch `agents/handoff-2026-09-12-0620`. Treat it as the restart authority. Then recheck the live heads of:

- `cmbant/QIprojects:main`
- `cmbant/reasoner:formal-research-lean`

Also recheck the blob of `QI-A/paper/finite_copy_quantum_memory.tex`. At handoff time the pins were:

- QIprojects main: `a3960aa4542eeed8ae785fceac78aaf8c0319031`
- manuscript blob: `6f4af839cc7c13b0cb2b3704fcefdeb1d88e9195`
- reasoner `formal-research-lean`: `2b1aacaef0c53adf709b08c19a9ecb1ca4207033`
- pinned mathlib: `52b284ff128a523eca1f67c68d677861b95cc002`

If the manuscript blob is unchanged, continue from the existing source audit rather than restarting it. If it changed, re-audit the affected theorem text before implementation.

The current QI-A lower-bound chain already includes coherent-power separation, Hermitian/rank-one spanning, canonical trace adjoints, ordinary positivity transport, POVM pullback, density-matrix `≤ I`, explicit isotypic auxiliary projectors/states, and the direct-sum deferred-query theorem `multiplicityMemoryDimension_le_of_deferredStatsOnIsotypicCoherentFamily`.

The main next frontier is **the physical symmetric-copy / Schur-isotypic realization that justifies the current explicit linear equivalence into `isotypicDirectSumCarrier d g` and the manuscript's symmetry-reduction channel**. Inspect the pinned mathlib APIs first (finite-dimensional unitary/isometry, tensor/symmetric powers, representation/isotypic decomposition, completely positive maps). Take the smallest genuine source-faithful bridge that turns one current external premise into a proved fact. Avoid convenience wrappers that do not close a manuscript dependency.

After that, prioritize:

1. concrete symmetry-reduction / commutant / multiplicity-algebra channel realization;
2. complete-positivity/CPTP semantics where needed — while keeping ordinary positivity results explicitly distinct from CP/CPTP;
3. coherent-width CPTP/Schmidt-number bridge and the explicit classically flagged upper construction;
4. operational classical-memory iff once the physical channel model exists.

Important scope discipline:

- Do not claim the QI-A main theorem is end-to-end Lean-certified.
- Do not call ordinary positivity complete positivity or CPTP.
- Do not invent a canonical Hilbert structure on Mathlib's algebraic `SymmetricPower`; the current finite Euclidean realization is supplied explicitly.
- Preserve theorem-local trust distinctions from the handoff, including the T39 `native_decide` finite table and external analytic Haar identity.

For every Lean PR, use this merge discipline:

1. Branch from the current `formal-research-lean` head.
2. Keep the theorem/module small and source-faithful.
3. No `sorry` or `admit`.
4. Use a temporary branch-only GitHub Actions workflow when needed.
5. Build the smallest changed module(s) first.
6. Once focused-green, freeze theorem source.
7. Add the module(s) to `FormalResearch.lean` and run full `lake build FormalResearch` on the exact promoted tree.
8. Record the exact tested candidate SHA and Actions run.
9. Delete only the temporary workflow after green.
10. Compare tested candidate to cleanup head and require that no Lean source/import bytes changed.
11. Recheck `QIprojects:main` and the manuscript blob immediately before merge.
12. Mark the PR ready and merge with `expected_head_sha` equal to the verified cleanup head.
13. Verify `formal-research-lean` moved to the merge commit.

If CI fails, fetch the exact Lean job log and repair only the concrete proof/API issue; do not weaken the theorem just to get green. Do not merge on a focused build alone.

Keep the user informed with concise progress updates during long tool sequences. When the user says “Continue”, continue the repository work immediately; do not ask what to do next unless there is a real blocker.

---
