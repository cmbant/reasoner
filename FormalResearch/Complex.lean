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
public import FormalResearch.Complex.HadamardGrowth
public import FormalResearch.Complex.HardyFejerRiesz
public import FormalResearch.Complex.HardyHalfPlane
public import FormalResearch.Complex.HardyArcDecay

/-!
# Complex analysis: Hadamard factorization and Fejér–Riesz arc bounds

Aggregate module for `FormalResearch/Complex/` (namespaces `FormalResearch.Hadamard` and `FormalResearch.Hardy`).  Mathlib has Jensen's formula,
Borel–Carathéodory and the canonical decomposition of an entire function, but no Hadamard factorization theorem; this
directory proves it, and applies it to the Airy function.  It also holds an elementary Fejér–Riesz inequality on the disc and its
half-plane arc form (`Hardy*`, Airy-free).

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
  z/a_n) e^{z/a_n}` (`airyAiC_hadamard`);
* `HadamardGrowth`: the converse growth bound: for `p ≤ s ≤ p+1` and `Σ ‖a_i‖^{-s} < ∞`, `‖E_p(w)‖ ≤ exp(K‖w‖^s)`, the canonical
  product satisfies `|f(z)| ≤ C exp(C|z|^s)` (`norm_canonProd_le`, `growthBound_canonProd`), and so does `c z^m e^{P} ∏ E_p(z/a_i)` with
  `deg P ≤ p` (`growthBound_factorization`): finite genus gives finite order, an upper bound only.

* `HardyFejerRiesz`: the Fejér–Riesz inequality on the unit disc (`fejerRiesz_disc`): `h` holomorphic on the open disc and continuous on
  the closed disc (`DiffContOnCl`, not only polynomials) satisfies `∫_{-1}^1 ‖h‖ ≤ (1/2) ∫_{-π}^{π} ‖h(e^{iθ})‖`; elementary proof (Blaschke
  division at a zero-free radius, `q = r r̄`, no Hilbert inequality), no Hardy-space theory;
* `HardyHalfPlane`: Möbius transport to the upper half-plane and the arc bound `hardy_arc_le`: for `G` holomorphic on `ℍ`, continuous on the
  closure with `‖G(z)‖(1+‖z‖)³ ≤ C`, `a ∫_0^π ‖G(a e^{iφ})‖ dφ ≤ (1/2) ∫_ℝ ‖G‖` for every `a > 0`;
* `HardyArcDecay`: the same under polynomial growth and integrable boundary values (`hardy_arc_le_poly`, by the damping factor
  `(1 - iδz)^{-K}`), and `hardy_arc_tendsto_zero`: the arc integral tends to `0` as `a → ∞`.
  Not formalised there: Hardy spaces `H^p(ℍ)` as notions, the Poisson representation of `G` on `ℍ` and the horizontal `L¹` bound
  `∫ ‖G(x+iy)‖ dx ≤ ∫ ‖G(x)‖ dx` (Lemma H of the Airy sampling bound), and the pointwise bound `‖G(z)‖ ≤ ‖g‖₁/(π Im z)`.

Layering: only `HadamardAiry` imports `FormalResearch.Special.Airy*` modules; no module of the `Airy` aggregate imports this
aggregate (the product of `Ai'`, `FormalResearch.Special.airyDeriv_hadamard` in `Special/AiryCft2DerivHadamard`, imports `HadamardAiry`
and is imported by `FormalResearch.Special`).
Not formalised: order = convergence exponent and lower bounds on canonical products (the converse is an upper growth bound only,
and only for `deg P ≤ p ≤ s ≤ p+1`, not the excess-genus case), the closed value of `Ai'(0)/Ai(0)` inside the product form, the
product for `Bi`; orders are not defined as notions (`hadamard` takes any `p` with `σ < p + 1` and the exact growth form).
-/
