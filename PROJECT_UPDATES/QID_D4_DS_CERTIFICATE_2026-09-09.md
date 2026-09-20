# QI-D D4 exact DS certificate — 2026-09-09

Source authority was re-audited against `cmbant/QIprojects:main` at `cf5bb7ea42362d9557172a1df96ff1d567da2fe5`.

The source certificate remains `QI-D/code/certify_ds_strict_D4.py` with its committed verification log. The theorem-relevant source bytes were unchanged across the recent QIprojects planning/research wave.

## Lean scope

The new modules are:

- `FormalResearch.QID.D4DoublyStochasticCertificate`;
- `FormalResearch.QID.D4DoublyStochasticDualCertificate`.

Lean checks the finite exact certificate layer:

- `|W(D4)| = 192` for the even signed-permutation representation;
- fundamental-coweight orbit sizes `(8,24,8,8)`;
- the rational witness value `<F,A> = 7/6`;
- Weyl support at most `1`, with attainment;
- exactly `2304` coweight-orbit constraints and zero witness violations;
- the printed 14 active dual pairs are members of the finite constraint family with bound `1/2`;
- their `1/6`-weighted outer products sum exactly to `F`;
- the exact dual objective is `7/6`.

The theorem identifying the finite coweight inequalities with semantic membership in `DS(W(D4))`, and the general convex-hull facet interpretation, remain explicit external bridge inputs. Thus this is an exact finite certificate formalization, not a hidden formalization of the whole generalized-Birkhoff theory.

## Validation

A development-branch module gate passed at head `662f10e81b5cac143c9f734a7804608b59b8f5e1`, GitHub Actions run `34373856596`, including placeholder rejection and hard builds of both D4 modules.

This clean branch is based directly on the current maintained `formal-research-lean` after QI-B U(1) PR #11 and adds the two D4 modules to `FormalResearch.lean`. A fresh full-aggregate gate is required before promotion/merge.

## Current source context

QIprojects now also proves the stronger all-rank nested type-D law `max_{T in DS(W(D_n))} <N_n,T> = n + 2/3` for every `n >= 4`. The D4 witness formalized here is the exact base/lower witness for that programme. Future Lean work should not reduce the all-rank theorem to the easy scalar budget alone; it should capture the symbolic decomposition/support interface if selected.
