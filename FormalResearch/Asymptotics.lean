module

public import FormalResearch.Asymptotics.UniformExpansion
public import FormalResearch.Asymptotics.TaylorUniform
public import FormalResearch.Asymptotics.AnalyticGerm
public import FormalResearch.Asymptotics.Examples

/-!
# Uniform asymptotic expansions in a parameter

Aggregate module for `FormalResearch/Asymptotics/`:

* `UniformExpansion`: `HasExpansionAlong`, `HasUniformExpansion`, `HasUniformExpansionOn` and their
  algebra (sum, scalar multiple, Cauchy product, composition, uniqueness, leading term, even
  expansions);
* `TaylorUniform`: uniform Taylor remainder of a jointly smooth `G : E × ℝ → F`;
* `AnalyticGerm`: the bridge `f z i = G (z, ε i)` with `G` smooth/analytic implies
  `HasUniformExpansion f (taylorCoeff G) ε l K`;
* `Examples`: the `3j` even expansion of Weyl P2 (`thm:3jeven`) as a corollary.
-/
