module

public import FormalResearch.CFT.ClarkTwoNode
public import FormalResearch.CFT.TwoEdgePoissonCore
public import FormalResearch.CFT.TwoEdgeVanDerCorput
public import FormalResearch.CFT.TwoEdgePoisson
public import FormalResearch.CFT.PaperII.Constants
public import FormalResearch.CFT.PaperII.SlitStrip
public import FormalResearch.CFT.PaperII.Rigidity

/-!
# CFT Modular Bootstrap Umbrella Module

Collects the Lean 4 formalization of shared Paper I / Paper II analytic results
and Paper II Airy-scale lower-bound and rigidity results:

- `FormalResearch.CFT.ClarkTwoNode`: Clark two-node sign uncertainty (`clark_airy.tex` Theorem 1.2)
  and Fold-Tip Seed Lemma (`fold_tip_theorem.tex` Lemma `ft:seed`).
- `FormalResearch.CFT.TwoEdgePoissonCore`: Universal two-edge strip Poisson bounds (Lemma `TE.1`),
  Stirling bound (`(TE.7)`), and `TE.2` fixed-point closures (`two_edge_bootstrap.tex`).
- `FormalResearch.CFT.TwoEdgeVanDerCorput` & `FormalResearch.CFT.TwoEdgePoisson`: Van der Corput
  oscillatory edge bounds (Lemma `TE.1a`) and `teb_edge_osc`.
- `FormalResearch.CFT.PaperII.Constants`: Paper II Airy-scale constants (`xiStar`, `lambdaV`,
  `xiBar`, `betaTip`, `Aopt`, `LStar`) and local extremal `phiStar`.
- `FormalResearch.CFT.PaperII.SlitStrip`: Slit-strip fold involution, Lemma `E`, Lemma `S`,
  `2.228 δ^(3/2)` deficit bound, Proposition `M`, and Theorem `A` (`log_free_optimality.tex`).
- `FormalResearch.CFT.PaperII.Rigidity`: Generalized Scheffé Lemma, Theorem `C`
  (`local_airy_model.tex`), and Theorem `R` `(R1)`–`(R3)` (`rigidity.tex`).
-/
