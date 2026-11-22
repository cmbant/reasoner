module

public import FormalResearch.Complex.StripPoisson
public import FormalResearch.Asymptotics.StirlingHalfInt
public import FormalResearch.Analysis.VanDerCorput
public import FormalResearch.TwoEdgeBootstrap.FixedPoint
public import FormalResearch.TwoEdgeBootstrap.EdgeOsc
public import FormalResearch.TwoEdgeBootstrap.FoldTipSeed

/-!
# Universal Two-Edge Bootstrap and Fold-Tip Seed (`CFT/common/two_edge_bootstrap.tex`, `ft:seed`)

Umbrella for shared CFT bootstrap machinery:

* Shared analytic foundations re-exported: `FormalResearch.Complex.StripPoisson` (Lemma `TE.1`),
  `FormalResearch.Asymptotics.StirlingHalfInt` (`(TE.7)`), and `FormalResearch.Analysis.VanDerCorput`.
* `FixedPoint`: `TE.2` logarithmic and polynomial absorption fixed-point closures.
* `EdgeOsc`: Lemma `TE.1a` dyadic oscillatory edge estimates (`teb_edge_osc*`).
* `FoldTipSeed`: Lemma `ft:seed` (`fold_tip_seed_lemma`).
-/
