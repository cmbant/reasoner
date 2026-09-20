# Quartic reconstruction bridge review note

Source authority audited at `cmbant/QIprojects:main` commit `a32a35809edd12b7d7cb7c23b332edad36efa5bc`.

The Lean source itself was hard-verified at exact code head `1dc24e93c1483782dd80b162c9b48cd26707fc41` in GitHub Actions run `34336956345`, which passed placeholder rejection, the new module build, and `lake build FormalResearch`.

Later commits on this feature branch only add/update handoff/review documentation and remove the temporary branch-local validation workflow; they do not change the verified `.lean` source.

The theorem boundary is intentionally conditional: the exact source CAS reconstruction equality and analytic hypotheses remain explicit assumptions. The new module checks the scalar prefactor sign, combines it with the existing quartic sign algebra, and performs the final unsquaring.
