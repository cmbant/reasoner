module

public import FormalResearch.Complex.StripPoisson
public import FormalResearch.Asymptotics.StirlingHalfInt
public import FormalResearch.Analysis.VanDerCorput
public import FormalResearch.TwoEdgeBootstrap.FixedPoint
public import FormalResearch.TwoEdgeBootstrap.EdgeOsc
public import FormalResearch.TwoEdgeBootstrap.Bootstrap
public import FormalResearch.TwoEdgeBootstrap.WeakFeedback
public import FormalResearch.TwoEdgeBootstrap.FoldTipSeed

/-!
# Universal Two-Edge Bootstrap and Fold-Tip Seed (`CFT/common/two_edge_bootstrap.tex`, `ft:seed`)

Umbrella for shared CFT bootstrap machinery:

* Shared analytic foundations re-exported: `FormalResearch.Complex.StripPoisson` (Lemma `TE.1`),
  `FormalResearch.Asymptotics.StirlingHalfInt` (`(TE.7)`), and `FormalResearch.Analysis.VanDerCorput`.
* `FixedPoint`: `TE.2` logarithmic and polynomial absorption fixed-point closures.
* `EdgeOsc`: Lemma `TE.1a` dyadic oscillatory edge estimates (`teb_edge_osc*`, improper limit
  `teb_edge_osc_tendsto`).
* `Bootstrap`: Theorem `TE.2(1)–(4)` abstract bootstrap closures (including the Hermite–Biehler
  multi-node extension) and Corollary `TE.4` (`teb_mellin_o1_lower`).
* `WeakFeedback`: Theorem `TE.2(5)` vacuum error and weak feedback extension (`teb_weak_part1`,
  `teb_weak_K_log_bound`, `teb_weak_feedback_closure`).
* `FoldTipSeed`: Lemma `ft:seed` (`fold_tip_seed_lemma`).
-/
