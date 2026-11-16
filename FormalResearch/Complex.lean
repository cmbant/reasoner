module

public import FormalResearch.Complex.HadamardProduct
public import FormalResearch.Complex.HadamardProductOrder
public import FormalResearch.Complex.HadamardListing
public import FormalResearch.Complex.HadamardCount
public import FormalResearch.Complex.HadamardCauchy
public import FormalResearch.Complex.HadamardBlaschke
public import FormalResearch.Complex.HadamardCore
public import FormalResearch.Complex.HadamardRadii
public import FormalResearch.Complex.HadamardDefect
public import FormalResearch.Complex.HadamardMain
public import FormalResearch.Complex.HadamardGeneral
public import FormalResearch.Complex.HadamardAiry

/-!
# Complex analysis: Hadamard factorization of entire functions of finite order

Aggregate module for `FormalResearch/Complex/` (namespace `FormalResearch.Hadamard`).  Mathlib has Jensen's formula,
Borel–Carathéodory and the canonical decomposition of an entire function, but no Hadamard factorization theorem; this
directory proves it, and applies it to the Airy function.

* `HadamardProduct`: elementary factors `E p`, canonical products `canonProd p a` over a family `a` with
  `Σ ‖a i‖^{-(p+1)} < ∞` (`hasProd_E`: locally uniform convergence; entire; zero set exactly `{a i}`; logarithmic derivative);
  `HadamardProductOrder`: the order of vanishing of `canonProd` at `w` is `#{i : a i = w}`;
* `HadamardListing`: a family `Listing f a` listing the non-zero zeros of an entire `f` with multiplicity (`exists_listing`);
* `HadamardCount`: Jensen counting, `|f| ≤ C exp(C|z|^σ)` gives `Σ ‖a i‖^{-s} < ∞` for `s > σ`;
* `HadamardCauchy`, `HadamardBlaschke`, `HadamardCore`, `HadamardRadii`: Cauchy bounds, the Blaschke decomposition on a disc
  with Borel–Carathéodory, the core estimate for the `p`-th derivative of `f'/f - Σ_{|a_i|<R}(z/a_i)^p/(z-a_i)`, and good
  radii on which it tends to `0`;
* `HadamardDefect`: the `p`-th derivative of that defect vanishes, so the defect is a polynomial of degree `< p`
  (a derivative route replacing lower bounds on canonical products on circles);
* `HadamardMain`, `HadamardGeneral`: **the Hadamard factorization** `f(z) = c z^m e^{P(z)} ∏ E_p(z/a_i)`, `deg P ≤ p`,
  `P(0) = 0`, for entire `f` with `|f| ≤ C exp(C|z|^σ)`, `σ < p+1` (`hadamard`, `hadamard_floor`, `hadamard_exists`),
  any index type, zero at `0` allowed;
* `HadamardAiry`: the genus-one product of the Airy function (order `3/2`), `Ai(z) = Ai(0) exp((Ai'(0)/Ai(0)) z) ∏ (1 -
  z/a_n) e^{z/a_n}` (`airyAiC_hadamard`).

Layering: only `HadamardAiry` imports `FormalResearch.Special.Airy*` modules; no `Airy` module imports this aggregate.
Not formalised: the converse (a canonical product of finite genus has finite order), order = convergence exponent, lower
bounds on canonical products, the closed value of `Ai'(0)/Ai(0)` inside the product form, the products for `Ai'` and `Bi`;
orders are not defined as notions (`hadamard` takes any `p` with `σ < p + 1` and the exact growth form).
-/
