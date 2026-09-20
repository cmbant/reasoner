# QI-A T07 finite code-dimension certificate — 2026-09-10

## Authority and source match

Research/certificate authority was rechecked at `cmbant/QIprojects:main` commit

`6080f36ddd7a3c85015416b793e0562caf685e5a`.

Canonical T07 inputs:

- `QI-A/notes/SECTOR_LABEL_ONLY_MEMORY.md`, blob `0cea876048473063a59fcbde4c8f030a740ae049`;
- `QI-A/scripts/verify_sector_label_only_memory.py`, blob `6fdee802f3d0eb55c0381083e40b09e465f7e01a`;
- `QI-A/notes/T07_REPORT.md`.

The current QIprojects delta through this pin contains no later QI-A source change. The source correction is preserved: the unrestricted physical block-curve converse is false. The statements formalized here are only for the narrower sector-label-only architecture with their identifying-query/guessing hypotheses kept explicit.

## Lean content

Added `FormalResearch/QIA/SectorLabelOnlyCodeDimension.lean` and imported it from `FormalResearch.lean`.

The module proves the finite-dimensional trace-budget layer behind T07 Lemmas 2.1 and 2.2:

- for positive decoder effects `B_j` and encoded states satisfying `omega_j <= I`, the exact complex PSD trace pairing gives `Re Tr(B_j omega_j) <= Re Tr(B_j)`;
- a POVM normalization `sum_j B_j = I_q` therefore gives total correct-message score at most `q` and uniform average success at most `q/N`;
- from explicit ideal identifying success and total-variation/deficiency comparison hypotheses, this gives the source conditional lower bound `delta >= 1 - eta - q/N`;
- with a free physical sector label and weights `p_j(lambda) <= ell(lambda)`, the weighted success is at most `q * sum_lambda ell(lambda) / N`; taking `ell(lambda)=max_j p_j(lambda)` is the source global `q L_d/N` bound;
- the corresponding global deficiency consequence is derived with the operational ideal-success and TV premises explicit.

The standard density-operator implication `omega <= I` is intentionally an explicit hypothesis rather than a newly built spectral-density framework.

## Verification

An initial compile failed only on two `noncomputable` annotations and one proof step after simplification; no theorem statement changed. The repaired conditional module passed run `34445272315`. The global label-leakage extension then passed its dedicated module run `34445548898`.

Exact promoted Lean tree:

`ed773873152e4d60f690f665ed14bdbdfaef77f1`.

Exact module blob:

`d416fe01e1c34eb6de824dd2bfb2360f27e336ae`.

Exact `FormalResearch.lean` blob:

`fd7956089fba6ae5c1f3678d119daebe6a9d1c2d`.

GitHub Actions promotion run:

`34445813054`.

That run passed:

1. rejection of `sorry` / `admit`;
2. `lake build FormalResearch.QIA.SectorLabelOnlyCodeDimension`;
3. full `lake build FormalResearch`.

The temporary workflow was removed after validation. No Lean theorem/module or aggregate-import bytes changed after the cited promoted tree.

## Scope boundary

This does **not** formalize the entire T07 approximate-memory theorem. In particular it does not prove:

- the regular Bergman/packing asymptotics or polynomial-rate exponents;
- the conditional multiplicity fidelity/orbit-overlap lemma;
- the mutual-information/Fano form of Lemma 2.3;
- the Gaussian/Szego critical-density theorem;
- finite-QI-A critical transfer;
- any unrestricted-physical block-curve converse (the source disproves that claim).

The result is the exact finite PSD/POVM coding/guessing layer, with operational bridge assumptions visible in the Lean theorem statements.
