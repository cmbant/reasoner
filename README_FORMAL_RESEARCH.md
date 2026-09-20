# Formal research verification spine

The `master` branch contains the maintained Lean/mathlib formalizations for exact load-bearing claims in the quantum-information, recoupling, and Gaudin research programme.

The former `formal-research-lean` development branch was squash-merged into `master` on 2026-09-20. New Lean work should branch from `master` and target `master`.

A claim is marked kernel-checked only after GitHub Actions compiles it without `sorry`.

Initial targets:

1. finite-field certificate lifting used by QI-C;
2. the square-root-free exact matrix identity behind the QI-A three-copy four-qubit chirality block;
3. an exact determinant/rank witness for the explicit D5 exceptional facet normal from QI-D.

See `THEOREM_MAP.md` for source-to-formal-statement traceability and the current trust boundary.
