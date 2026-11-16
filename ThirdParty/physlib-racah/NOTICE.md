# Vendored: Racah-formula bridge for Physlib's operator-defined `sixJ` (our own work, pending upstream)

- Source: <https://github.com/cmbant/physlib> (fork of `leanprover-community/physlib`), branches `racah/01-rising-factorial` … `racah/24-sixj-racah-all`
  (a stack, one commit and one new file each; tip `df2a8eea8d79e2185bba844db9313ef12f294cc0`).
- Base: upstream Physlib `master` at `3d9ca099e0c842e746bef6f10289a6f965bc8f08` (Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, the same pin as this repo).
- Licence: Apache-2.0 (`LICENSE`, copied verbatim from Physlib). The files are written by the repository owner for Physlib; no Physlib file is modified except the one-line module import in `PhyslibAlpha.lean` and one line of `scripts/lint/exemptions/Theorems.txt`, both carried only in `patches/`.
- Status: no Physlib PR has been opened (a human must open and describe it). This copy exists so the work lives in this repository until/unless Physlib accepts it. When it is merged upstream, delete this directory.

Contents

- `PhyslibAlpha/...`: the 24 new files, byte-identical to the fork's `racah/24-sixj-racah-all` tree (3944 lines), under their Physlib module names.
- `patches/0001…0024-*.patch`: `git format-patch` of the stack against the base commit (apply with `git am`; produces exactly the tree of `racah/24-sixj-racah-all`).
- `check.sh`: applies the patches to a clean Physlib checkout at the base commit and builds the new modules.

Main theorems: `sixJ_eq_ite_racah6j` (`PhyslibAlpha/QuantumMechanics/AngularMomentum/SixJRacahAll.lean`): for all `a b c` with `0 < a+b`, `0 < b+c`, Physlib's operator-defined `sixJ` equals Racah's closed formula when `ValidA ∧ ValidB` and is `0` otherwise (vanishing for inadmissible labels is the definition of `sixJ`; `validA_and_validB_iff` states admissibility as the four triangle conditions and `2K ≤ a+b+c`).
It rests on `sixJ_eq_racah6j` (`SixJRacah.lean`, `0 < a`, `0 < c`) and the edge cases `a = 0`, `c = 0` (`SixJEdge`, `RacahEdge`, `SixJRacahEdge`, proved directly at `M = J`, not via Sears).
Axioms `[propext, Classical.choice, Quot.sound]`. Not covered: the operator-side three-term recurrence. Route for `0 < a`, `0 < c`: `sixJ = Cconst · Xs`, `Xs` a balanced terminating `₄F₃`, one Sears transformation.

Build in this repository

- Files 01–04 (`PhyslibAlpha/Mathematics/SpecialFunctions/Hypergeometric/{RisingFactorial,Saalschutz,SearsTerms,Sears}.lean`: Pfaff–Saalschütz and Sears for terminating balanced series) import only Mathlib and form the optional library `PhyslibRacahHyp`
  (`lake build PhyslibRacahHyp`). It is not in `defaultTargets` and nothing in `FormalResearch` imports it.
- Files 05–24 import Physlib modules (`Wigner3j`, `SixJ`, `SixJSymmetry`, `ClebschGordanFormula`, …), so they build only inside a Physlib checkout; use `check.sh`. This repository does not depend on Physlib.
- Module names are Physlib's (`PhyslibAlpha.*`), not renamed, so that the files can be diffed against and moved into Physlib unchanged.
