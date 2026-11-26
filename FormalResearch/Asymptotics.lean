module

public import FormalResearch.Asymptotics.UniformExpansion
public import FormalResearch.Asymptotics.TaylorUniform
public import FormalResearch.Asymptotics.AnalyticGerm
public import FormalResearch.Asymptotics.Examples
public import FormalResearch.Asymptotics.DominatedSeries
public import FormalResearch.Asymptotics.CenteredPowerSum
public import FormalResearch.Asymptotics.LogSeries
public import FormalResearch.Asymptotics.GeometricExpansion
public import FormalResearch.Asymptotics.ExpExpansion
public import FormalResearch.Asymptotics.StirlingHalfInt
public import FormalResearch.Asymptotics.DyadicAbsorption
public import FormalResearch.Asymptotics.BinetRemainder
public import FormalResearch.Asymptotics.SymbolClass

/-!
# Uniform asymptotic expansions in a parameter

Aggregate module for `FormalResearch/Asymptotics/`:

* `UniformExpansion`: `HasExpansionAlong`, `HasUniformExpansion`, `HasUniformExpansionOn` and their
  algebra (sum, scalar multiple, Cauchy product, composition, uniqueness, leading term, even
  expansions);
* `TaylorUniform`: uniform Taylor remainder of a jointly smooth `G : E × ℝ → F`;
* `AnalyticGerm`: the bridge `f z i = G (z, ε i)` with `G` smooth/analytic implies
  `HasUniformExpansion f (taylorCoeff G) ε l K`;
* `Examples`: the `3j` even expansion of Weyl P2 (`thm:3jeven`) as a corollary;
* `DominatedSeries`: uniform Tannery theorem for finite sums with varying index sets (used by the
  Mehler–Heine formula, `FormalResearch/Special/JacobiMehlerHeine.lean`);
* `CenteredPowerSum`: `S_{2r}(p) = ∑_{q=-(p-1)/2}^{(p-1)/2} q^{2r} = 2B_{2r+1}((p+1)/2)/(2r+1)`;
* `LogSeries`: Mercator series `∑ log(1 - y_i) = -∑_n (∑ y_i^n)/n` for a finite family;
* `GeometricExpansion`: a convergent power series with geometrically bounded coefficients is a
  `HasUniformExpansion`;
* `ExpExpansion`: `exp` of an expansion with `a_0 = 0` is an expansion with the coefficients of the
  formal exponential (`HasExpansionAlong.exp`, `expCoeff`);
* `StirlingHalfInt`: half-integer Gamma and factorial Stirling bounds (`gamma_add_half_le`,
  `teb_stirling_bound`);
* `BinetRemainder`: Binet's integral remainder `B_Bin(w)`, all-order derivative bounds, and vertical
  strip bounds (`binetRem_iteratedDeriv_norm_le`, `binetDiff_*`);
* `SymbolClass`: classical Airy symbol classes `𝒮_β` / `𝒬_β` (`IsSymbolOn`, `IsSymbol`,
  `IsWeightedSymbolOn`) and algebra/composition closure (Lemma `W.0`).
-/
