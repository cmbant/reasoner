module

public import FormalResearch.Special.JacobiDef
public import FormalResearch.Special.JacobiInt
public import FormalResearch.Special.JacobiBasic
public import FormalResearch.Special.JacobiRec
public import FormalResearch.Special.JacobiOrth
public import FormalResearch.Special.JacobiBeta
public import FormalResearch.Special.JacobiOrthReal
public import FormalResearch.Special.JacobiSpecial
public import FormalResearch.Special.JacobiZeros
public import FormalResearch.Special.JacobiCD
public import FormalResearch.Special.GammaRatio
public import FormalResearch.Special.JacobiMehlerHeine
public import FormalResearch.Special.JacobiMehlerHeineRate
public import FormalResearch.Special.JacobiBessel
public import FormalResearch.Special.LaguerreHardEdge
public import FormalResearch.Special.LaguerreUniqueness
public import FormalResearch.Special.Airy
public import FormalResearch.Special.SturmAiryZeros
public import FormalResearch.Special.SturmAiryComparison
public import FormalResearch.Special.SturmAiryInterlace
public import FormalResearch.Special.AiryPruferLift
public import FormalResearch.Special.AiryPruferZeros
public import FormalResearch.Special.SturmAiryLevels
public import FormalResearch.Special.SturmAiryPruferUnique
public import FormalResearch.Special.SturmAiryNodes
public import FormalResearch.Special.DiscreteJacobiCalculus
public import FormalResearch.Special.DiscreteJacobiCalculusVolterra
public import FormalResearch.Special.DiscreteJacobiCalculusComparison
public import FormalResearch.Special.DiscreteJacobiExtras
public import FormalResearch.Special.DiscreteJacobiExtrasHardEdge
public import FormalResearch.Special.DiscreteJacobiExtrasGronwall
public import FormalResearch.Special.LangerPhi
public import FormalResearch.Special.LangerHadamard
public import FormalResearch.Special.LangerJets
public import FormalResearch.Special.LangerCoordinate
public import FormalResearch.Special.AiryParametrixPoly
public import FormalResearch.Special.AiryParametrixShift
public import FormalResearch.Special.AiryParametrixTaylor
public import FormalResearch.Special.AiryParametrixSkeleton
public import FormalResearch.Special.AiryParametrixPointwise
public import FormalResearch.Special.AiryParametrixJets
public import FormalResearch.Special.AiryParametrixDefect
public import FormalResearch.Special.AiryParametrixLattice
public import FormalResearch.Special.AiryRecessiveSums
public import FormalResearch.Special.AiryRecessiveKernel
public import FormalResearch.Special.AiryRecessive
public import FormalResearch.Special.AiryRecessiveSelection
public import FormalResearch.Special.AiryWindow
public import FormalResearch.Special.AiryWindowMain
public import FormalResearch.Special.AiryWindowSharpEnergy
public import FormalResearch.Special.AiryWindowSharp
public import FormalResearch.Special.AiryWindowTaylor
public import FormalResearch.Special.AiryParametrixLanger
public import FormalResearch.Special.AiryParametrixUniformCh
public import FormalResearch.Special.AiryParametrixUniformODE
public import FormalResearch.Special.AiryParametrixUniformPointwise
public import FormalResearch.Special.AiryParametrixUniformDefect
public import FormalResearch.Special.AiryParametrixUniformLattice
public import FormalResearch.Special.DiscreteAiryLimitData
public import FormalResearch.Special.DiscreteAiryLimitLattice
public import FormalResearch.Special.DiscreteAiryLimitDefect
public import FormalResearch.Special.DiscreteAiryLimitHyp
public import FormalResearch.Special.DiscreteAiryLimitFields
public import FormalResearch.Special.DiscreteAiryLimitSetup
public import FormalResearch.Special.DiscreteAiryLimit
public import FormalResearch.Special.DiscreteAiryLimitHahnTurn
public import FormalResearch.Special.DiscreteAiryLimitHahn
public import FormalResearch.Special.DiscreteAiryLimitWindow
public import FormalResearch.Special.DiscreteAiryLimitHyperDecay
public import FormalResearch.Special.DiscreteAiryLimitHyperWindow
public import FormalResearch.Special.DiscreteAiryLimitChainsCore
public import FormalResearch.Special.DiscreteAiryLimitChains3j
public import FormalResearch.Special.DiscreteAiryLimitChains6j
public import FormalResearch.Special.DiscreteAiryLimitChainsHahnAiry
public import FormalResearch.Special.DiscreteAiryLimitChainsRacahAiry
public import FormalResearch.Special.DiscreteAiryLimitChains2Nodes
public import FormalResearch.Special.DiscreteAiryLimitChains2Twist
public import FormalResearch.Special.DiscreteAiryLimitChains2Racah
public import FormalResearch.Special.DiscreteAiryLimitChains2HalfAiry
public import FormalResearch.Special.DiscreteAiryLimitChains2Half3j
public import FormalResearch.Special.DiscreteAiryLimitChains2Half6j
public import FormalResearch.Special.DiscreteAiryLimitChains2Half6jFam
public import FormalResearch.Special.DiscreteAiryOscTurn
public import FormalResearch.Special.DiscreteAiryPhysChains
public import FormalResearch.Special.DiscreteAiryPhysRacah
public import FormalResearch.Special.DiscreteAiryKappaAll
public import FormalResearch.Special.DiscreteAiryUnifHahn
public import FormalResearch.Special.DiscreteAirySecondHahn
public import FormalResearch.Special.AiryCft2DerivHadamard
public import FormalResearch.Special.Barnes
public import FormalResearch.Special.Lattice
public import FormalResearch.Special.ComplexStirling
public import FormalResearch.Special.HermiteAiry
public import FormalResearch.Special.HermiteKappa
public import FormalResearch.Special.DiscreteLg

/-!
# Special functions: Jacobi polynomials

Jacobi polynomials `P_n^{(α,β)}` (DLMF 18): explicit-sum definition, differential equation,
derivative, reflection, three-term recurrence, orthogonality and norm (natural and real
parameters `α, β > -1`), zeros, Christoffel–Darboux, Rodrigues, and the Legendre, Chebyshev and
Gegenbauer special cases; the Mehler–Heine formula `n^{-α} P_n^{(α,β)}(cos(z/n)) → (z/2)^{-α} J_α(z)`
(`JacobiMehlerHeine`, `JacobiBessel`); the Laguerre recurrence of the hard-edge factor
(`LaguerreHardEdge`, with uniqueness of that solution up to scale in `LaguerreUniqueness`); the Airy function on `ℂ` and `ℝ`: definition by an absolutely convergent
contour integral, entire, `Ai'' = z Ai`, explicit decay, positivity on `[0,∞)`, real negative zeros, rotation
identity and `Bi` (`Airy`); Sturm and Prüfer theory of `y'' = q y` (`q` continuous, in particular the Airy
equation `q x = x`): simple zeros, Sturm separation and comparison, zero counts, Prüfer angle
(`SturmAiry*`, `AiryPrufer*`); the Airy side of the discrete-to-Airy limit (`Airy` aggregate: shift identity, Taylor
expansions, envelope weight); the Langer coordinate at a simple turning point (`LangerPhi`, `LangerHadamard`,
`LangerJets`, `LangerCoordinate`); the discrete Jacobi calculus for three-term recurrences (`DiscreteJacobiCalculus*`,
`DiscreteJacobiExtras*`: Lagrange/Casoratian identities, Green function, reduction of order, Volterra form, recessive
selection, final-value existence, hard-edge bridge, discrete Grönwall bounds); and the discrete-to-Airy comparison built on
it: the parametrix defect `|A(q+h/2)ψ(q+h) + A(q-h/2)ψ(q-h) - cψ(q)| ≤ K h²(1+|X|)³ airyWt X` for `ψ = g·Ai(h^{-2/3}ζ)`
under an assumed amplitude relation (`AiryParametrix*`: shift Taylor bounds, parity skeleton, pointwise and jet estimates,
lattice form); the amplitude relation `g²Aζ'Sh(ζζ'²) = 1` and the eikonal `Ch(ζζ'²) = u` for M3's own `ζ, g` near a simple
turn, with the combined window-form defect (`AiryParametrixLanger`, M7a); the uniform defect `≤ K h² airyWt X` with no
`(1+|X|)³`, for every real `X` including the turn neighbourhood, by expanding the shift functions at fixed `ζ`, with its
lattice and relative forms `≤ K h² |ψ_k|` (`AiryParametrixUniform*`, M7b); the recessive solution and second solution under a relative defect hypothesis (`AiryRecessive*`: kernel row
sums, exact solution `f` with `|f-ψ| ≤ Cδ³ψ`, selection `Y = κf + μ f₂`), and the bounded oscillatory window by a discrete
Grönwall march (`AiryWindow*`: `discrete_airy_window`, Taylor remainders of `Ai` on `[-A0,-1]`; `AiryWindowSharp*`: the energy march
`energy_march_down` and the abstract chain lemma `window_from_top_sharp` with the sharper constant `exp(3V/2)`, `V` the relative variation of the
local frequency, a power of `A0` instead of `e^{O(A0²)}`, not yet applied to `discrete_airy_window`); and the wiring layer that
composes all of these for a simple turn (`DiscreteAiryLimit*`): `discrete_airy_limit` (for one fixed smooth `u, A` with
`u(c₀) = 1`, `u'(c₀) > 0`, `A(c₀) > 0`: the exact recessive solution is `ψ = g·Ai(h^{-2/3}ζ)` within relative error `O(δ³)`
on `X ≥ 0` and within `O(δ³)` of the weight `W` on a bounded oscillatory window `X ≥ -A₀`, with the window positions exported,
and every solution with controlled end values is `κf + μf₂` with `μ` exponentially small), its bounded-window consequence
`dal_conclusion_window`, the closed-form Hahn / centred Racah instance `discrete_airy_hahn_racah(_window)`, the hard-edge
decay that discharges hypothesis (R) for the closed forms up to one normalisation `|Y_{k₁}| ≤ δ^{-p}` at an early forbidden-side
site (`DiscreteAiryLimitHyper*`: `hd_backward_decay`, `hr_hardedge_decay`, `discrete_airy_hahn_racah_hardedge(_window)`), and
the identification of the actual Wigner `3j`/`6j` chains (integer data) with the closed-form Hahn / centred Racah recurrences,
with the end conditions and the bound `|Ŷ| ≤ √N` from the Gauss weight, composed with the Airy limit
(`DiscreteAiryLimitChains{Core,3j,6j,HahnAiry,RacahAiry}`: `hahn_class_chain`, `racah_class_chain`, `hahn_chain_airy`,
`racah_chain_airy`).  The chain instances are completed by `DiscreteAiryLimitChains2*`: existence of lattice nodes of the `3j`
chain with the exact congruence obstruction (`hahn_node_exists`, `hahn_node_obstruction`, `hahn_chain_airy_infinite`), the `τ = -1`
branch by the `(-1)^k` twist (`jac_twist`, `hahn_chain_airy_neg`), the `6j` turn from the triangle geometry for both branches
(`racah_turn_geom_pos/_neg`, `racah_chain_airy_geom_pos/_neg`) together with the family of integral-triangle realisations
(`racah_realisation`, `racah_chain_airy_family_pos/_neg`), the abstract composition `airy_chain_compose`, and the half-integer
(shifted-index, `L = k + 1/2`) versions of the identification, `(R)`, nodes, realisations and the Airy limit
(`discrete_airy_hahn_racah_half`, `hahn_class_chain_half`, `racah_class_chain_half`, `hahn_chain_airy_half`,
`racah_chain_airy_geom_half_pos/_neg`).  Scope of the layers above: one fixed shape `(u, A, c₀)` (for the chains, one fixed
rational `x`, resp. `(α, β, x)`: an irrational shape has no exact node or realisation, and uniformity over compact families is
not proved), the recessive solution and a bounded oscillatory window `X ≥ -A₀`; the chains are for integer data and for the
shifted half-integer data of `3j` and of `6j` with `a, b, c ∈ ℤ`, `m, n ∈ ℤ + 1/2` (mixed-parity `6j` labels, and half-integer
Hahn with `x < 0`, are not covered); `κ` is not identified (no Darboux matching; `κ ≠ 0` is not part of these layers, it is `hahn_chain_kappa` below), constants are existential
(window constant `e^{O(A₀²)}`; the sharper `exp(3V/2)` is an abstract lemma, not wired in); the input cited by the papers (GBVA,
Geronimo) is still cited, not replaced.

The non-recessive pair and the whole oscillatory side are the next two layers.  `DiscreteAiryOsc*` (10 modules): variation of
constants for three-term recurrences with a weighted Grönwall march (`voc_march_up/down`, `VoC`), the generic and `Bi`
parametrix defects (`dao_defect_lattice`, `dao_bi_defect_lattice`; the M7b defect is not specific to `Ai`), the Casoratian of the
parametrix pair conserved up to `O(δ⁴)` (`DaoPair.cas_vary`, `dao_sum_p`), the two-sided decomposition (`dao_decomposition`,
`dao_up/down`), and `DaoConclusion` / `dao_turn_conclusion` for smooth data at a simple turn: exact `f ~ g·Ai`, `F₂ ~ g·Bi` to
`Cδ³` in the weights `airyWt`, `airyBiWt` on all of `[J, N]` with `q_J ∈ [c₀ - r, c₀ - r + δ³)` (the macroscopic oscillatory
side), constant Casoratian `≥ δ/C`, every solution `κf + μF₂` with `|μ|` exponentially small.  `DiscreteAiryPhys*` (5 modules):
the unified statement `DaiFull` / `discrete_airy_full` (`f`, `F₂` unique, comparison extended to `N+1`, pointwise
`Y = κ g Ai + μ g Bi + O(δ³)(|κ| airyWt + |μ| airyBiWt)` on `[J, N+1]`; it has the content of `dao_turn_conclusion` and of
`discrete_airy_limit` for its own radius, but does not formally derive them: each picks its own `r`, `N`, and the two recessive
solutions agree only when normalised at the same `N`, `dap_recessive_eq`), and the actual chains on that window
(`airy_full_compose`; Hahn `hahn_chain_airy_full` with `_neg`, `_infinite`, `_half` (the model case `M = σ = 0`, `x = 1/2`), Racah `racah_chain_airy_full_pos/_neg`,
`_family_pos/_neg`: fixed rational `x` at a lattice node, resp. integer data, constants depending on `(M, σ, x)`, radius `r ≤ q_*/4`
that of the Langer chart).  `DiscreteAiryKappa*` (39 modules, umbrella `DiscreteAiryKappaAll`) then determines `κ` for the actual `3j` chain (integers `M, σ`,
rational `x ∈ (0,1)`, `τ = +1`; every lattice node with `1/N ≤ ε₀` has the matching of `hahn_chain_airy_full` with constants depending on `(M, σ, x)`):
`hahn_chain_kappa` (`|κ| ≥ κ_min > 0`, `κ_min` independent of `N`, by a mass argument `N = ΣŶ² ≤ N sup Ŷ²`, `gaussWeight_3j`, `kf_mass_le`, with an a priori
bound on the whole chain by the values at the turn), the **order** `hahn_chain_kappa_order` (`c_lo ≤ κ² δ ≤ c_up`, `δ³ = 1/N`, i.e. `κ² ≍ N^{1/3}`; lattice sums of `Ai²`,
`kai_sum_lower`, `kai_sum_upper_bound`, against the Gauss weight `kk_mass_eq`) and the **sharp constant** `hahn_chain_kappa_sharp` (for every `τ > 0` and `1/N ≤ ε₁(τ)`:
`|κ² δ - 2| ≤ τ`, i.e. `κ² = 2N^{1/3}(1+o(1))`, `|κ| = √2 N^{1/6}(1+o(1))`; the amplitude of the second-order (Ermakov-Milne) invariant `kerm_invariant` is constant along the
oscillatory band to `O(S)` (`hahn3j_band_clean`) and equals `κ²δ/π(1+o(1))` at its end by the Airy matching with the chart identity `g² = 2√(-ζ)/α`, `KshChart.g2`, `ksh_bond_match`;
the band, left and zone masses add up to `N`, `ksa_combine`).  Its ingredients are of independent use: the first-order adiabatic invariant of a three-term recurrence
(`kiF_step`, `ki_invariant`: two-sided `e^{O(1)}` comparison over a band, `kl_band`), the second-order Ermakov invariant, the exact mass identity and band masses
(`kerm_mass_id`, `kp_band_mass`, `hahn3j_band_mass`), Riemann sums of `1/α` (`kr_sum_bounds`), the a priori left bound down to the hard edge
(`kl_hahn_left`), monotone decay on the forbidden side beyond the turn (`kr_chain_mono`) and the matching with the chart data exported
(`kc_hahn_full`, `kc2_hahn_full`; these repeat the proof of `discrete_airy_full` with extra conjuncts and may later be folded into it).  The rate is not uniform:
the proof gives `|κ² δ - 2| ≤ C₁ A + C₂(A) δ` for every small `A` (numerically the error is about `δ⁴`).  Still open: an explicit rate and uniformity in `x` (the hard
edges `x → 0, 1`), the Darboux phase and sign of `κ`, `κ ≠ 0` for `τ = -1`, Racah and half-integer chains, uniformity of the Racah/half-integer matching over families,
the half-integer version of the full statement, Racah family variants, explicit constants, analyticity of `ζ`.

Second order: `DiscreteAirySecond*` (20 modules, imported through `DiscreteAirySecondHahn`, which imports `DiscreteAirySecondTurn`, `DiscreteAirySecondHahnCoef` and
`DiscreteAirySecondLangerData`) prove the second-order bracket, abstractly and for the closed-form Hahn / centred-Racah chain (S4).
For smooth Langer-form data `(ζ, A, A₂, g, q₁, c₂)` (`ζ(c₀) = 0`, `ζ' > 0`, `A, g > 0`, amplitude relation `hrel`, the `q₁`-residual equation) the
exact solutions are `g·Ai(X + δ⁴q₁/g)` and `g·Bi(…)`, `X = ζ/δ²`, with error `δ⁶ = h²` in the Olver weights `airyWt`, `airyBiWt`
(`airy2_turn_conclusion`, `A2TurnConclusion`: macroscopic window `[c₀ - r, c₀ + r/4]`, Casoratian `≥ δ/Q`, coefficients within `E δ⁹` of the
second-order ones), and `q₁` is constructed on a ball `B(c₀, ρ)` from `ζ ∈ C⁷`, `A, g ∈ C⁶` (`airy2_turn_full`, `transport_regular_solution`,
`airy2_q1_exists`).  The pieces: the general-rate abstract machinery (`dao_conclusion_rate`, `dai_full_rate`, `DaiFullR`: `DiscreteAirySecondAbstract`),
the second-order shift coefficients and third-order remainders (`apu2_C_remainder`, `apu2_S_remainder`), the one-link expansion and the two-link
combination, the row defect `K δ⁹ airyWt` of the parametrix (`airy2_defect_Ai/_Bi`, `airy2_shifted_defect_Ai/_Bi`) and the window facts at a simple turn
(`a2t_window`).  This is weaker than the paper's `O(h³)` remainder.
The Hahn / centred-Racah instance (S4): the closed-form coefficients `A_k`, `c_k` are within `O(h⁴)` of the second-order forms `A + h²A₂`, `2Au + h²c₂`,
with `A₂ = ½ ẽ(q²) c_ab/q²`, `c_ab = 1/8 - (a² + b²)/2`, `c₂ = -τ[β₀(1/4 - (a² + b²)/2) + ab/q²]` (`hsc_coef_A`, `hsc_coef_C`,
`hs_perturb`: `DiscreteAirySecondHahnCoef`; this is the `η_π = 0` case of P3 `eq:class-a2b2`); the route from `u ∈ C⁷`, `A ∈ C⁶` to second-order Langer data
(`langer_hrel_seven`: `ζ ∈ C⁷`, `A, g ∈ C⁶`; `DiscreteAirySecondLangerData`); and the wiring (`hahn_airy2_turn`, `hahn_airy2_compose`:
`DiscreteAirySecondHahn`): `DaiFullR` at rate `δ⁶ = h²` for the actual closed-form chain on the window `[q* - ρ/2, q* + ρ/4]`
(`ρ` the Langer-chart radius, `q₁ ∈ C³` on a ball; bracket `Ai + h^{4/3}(q₁/g) Ai' + O(h²)`; for the composition, the bound (R) on `Y` is a hypothesis).
Not formalised: the `κ` normalisation and the second-order phase (Darboux identification of `q₁/g` with the paper's `ϖ`), the `q`-Racah chain
(`η_π ≠ 0`), half-integer / shifted-lattice and mixed-parity labels, uniformity in `x`, hard edges, a global `q₁` on the window, the paper's sharper `O(h³)` remainder;
the external input of `P3` (Geronimo–Bruno–Van Assche canonical basis and connection) is not replaced.

Uniformity in the shape: `DiscreteAiryUnif*` (10 modules, imported through `DiscreteAiryUnifHahn`) make the unified statement quantitative.
A `C²` jet calculus and an explicit Langer chart on a ball (`dun_chart`, `DiscreteAiryUnifJet`, `DiscreteAiryUnifChart`), explicit amplitude jets
(`dun_amp`, `DiscreteAiryUnifAmp`), the parametrix defect `≤ K δ⁶ airyWt`, resp. `airyBiWt`, from jet bounds alone (`dun_exact_defect`, `dun_lattice`,
`DiscreteAiryUnifDefect`, `DiscreteAiryUnifLattice`) and the assembly with explicit window data (`discrete_airy_full_win`, `DiscreteAiryUnifFull`) give
`discrete_airy_full_unif` (`DiscreteAiryUnifTheorem`, datum class `DunDatum` in `DiscreteAiryUnifMain`): for bounds `(ρ, Ku, m, a±, KA, E)` there are `r, δ₀, C,
Cmu, ξ₀` depending only on these such that `DaiFull` holds for every datum within the bounds (quantifier order `∀ bounds ∃ constants ∀ datum`).
`hahn_datum_unif` (`DiscreteAiryUnifHahnData`) checks the bounds for the `3j` datum uniformly in `y = τx ∈ [x₀, x₁] ⊂ (0,1)`, and `hahn_chain_airy_full_unif`,
`hahn_chain_airy_full_neg_unif`, `airy_full_compose_unif`, `discrete_airy_hahn_full_unif` (`DiscreteAiryUnifHahn`) give the actual `3j` chain with
`r, δ₀, C, Cmu, ξ₀` depending only on `(M, σ, x₀, x₁)`, for every lattice node `x_n ∈ [x₀, x₁]` (resp. `[-x₁, -x₀]`) and `1/N ≤ δ₀³`, with no parity
condition; this supersedes the fixed-`x` `hahn_chain_airy_full` for the shape, and covers approximate nodes `x_N → x*`.  Still open there: the hard-edge
degenerations `x → 0`, `x → 1` (constants degrade), `κ` uniform in `x`, uniform Racah and half-integer (shifted-lattice) versions, and the statement that
a continuous family over a compact parameter set satisfies the `DunDatum` bounds (checked by hand for the Hahn family only; compactness is used there only for fixed
functions of the chart variable, never in the datum parameter).

The `Airy` aggregate also holds the CFT consequences of the zeros of `Ai` (`AiryCft*`): the Mittag-Leffler expansion of `Ai'/Ai`
and the sum rules `Σ(z-a_n)^{-2} = (Ai'/Ai)² - z`, `Σ a_n^{-2} = (Ai'(0)/Ai(0))²`, the residue-defect formula (Theorem D) for entire
`f`, and the quadrature `∫_ℝ f = Σ f(a_n)/Ai'(a_n)²` (Corollary D1, `f` entire with `‖f(u)‖ ≤ C(1+|u|)^ν e(u)`, `ν < -1`); round two
(`AiryCft2*`) adds Theorem D for `f` holomorphic only on a disc (`airy_defect_ball`), the `Ai'` asymptotics on the negative axis for complex
phase, the zeros of `N = P Ai + Q Ai'` (real, simple, positive weights, indexed into the zeros of `Ai`), their good circles,
Theorem D and the quadrature `∫_ℝ f = Σ f(z) D/N'²` (`ν < -1`; constant real `P, Q`, `Q ≠ 0`), Clark-Airy summation for `ψ_α`
(`airyClark_quadrature`, `ν < -1`), the largest zero `a'_1` of `Ai'` with `S_1 = Σ (a_n - a'_1)^{-2} = |a'_1|`, and the Hadamard
product of `Ai'` (`airyDeriv_hadamard`; this module imports `Complex.HadamardAiry` and is imported here, not by `Airy`).  Theorem Q
of AIRY_POISSON, parts (1), (3), (4), is formalised for any real `ν` with `f ∈ L¹(ℝ)` (`AiryCftQ*`, via the Fejér–Riesz bounds of `Complex.Hardy*`): the limit form,
the sampling bound `Σ‖f(a_n)/Ai'(a_n)²‖ ≤ C ∫_{x<0}‖f‖` (`airyQ_sampling`) and the unconditional `HasSum` to `∫_ℝ f` (`airyQ_hasSum_unc`), also for
`P Ai + Q Ai'` and Clark-Airy (`airyNC_hasSum_unc`, `airyClark_hasSum_unc`).  Round five adds the sharp pointwise bound Q (2) with the constant `4π` (`airyQ_pointwise_sharp`), `𝒢_N ⊂ 𝒢_{1/2}` (`airyQ_mem_half`),
the vanishing moments (Corollary Q′, `airyQ_vanishing_moment`), the labelling of the Clark nodes by the gaps of `Ai` and their half-way location (`AiryClarkLabel*`), and the
Theorem B (sign uncertainty: the inequality, its sharpness and the full equality case `f = c Ai²/(u - a₁)`, `c < 0`, with the converse; `AiryCftSign*`).  Open: the Poisson representation of the unfolded
function (Lemma H), the Airy–Poisson identity (Theorem 1, Lemma 3), the node phase, polynomial `P, Q`, the note's Remark B.1.  The
Hadamard factorization theorem, the converse growth bound (`HadamardGrowth`) and the genus-one product of `Ai` are in the separate
aggregate `FormalResearch.Complex` (it imports `HadamardAiry`, which uses the Airy modules; no module of the `Airy` aggregate imports it).
Barnes' `G`-function and the Gamma identities of the Weyl W1 free-fermion paper (`Barnes*`, umbrella `Barnes`, namespace
`FormalResearch.Special.Barnes`; Mathlib has no Barnes `G`): Gauss' series `ψ(z) = -γ + ∑(1/(k+1) - 1/(k+z))` for `Complex.digamma` on
`Re z > 0` (`digamma_eq_series`; Mathlib has no Gauss series), the Weierstrass log series of `log G(1+z)` with termwise derivative
`z(ψ(1+z)+γ)` and the normalisation `G(2) = 1` from Stirling, `G` on `Re w > 0` with `G' = QG` (`barnesQ`), `G(w+1) = Γ(w)G(w)`, its
extension to an entire function `barnesG` with zero locus `{0,-1,-2,…}` and a zero of order exactly `m+1` at `-m`, the kernel
`cosh πξ + cos θ` and the Cauchy contour shift `∫ψ(½+ix/2)/(cosh πx+cos θ)dx = 2[Q(1+b) - Q(1-b)]/sin θ` (`integral_digamma_div_kerD`),
differentiation under the integral (`hasDerivAt_bgInt`), the real form of `thm:BG`, `-(1/4π)∫log((cosh πx+cos θ)/(cosh πx+1)) Re ψ(½+ix/2)dx =
log[G(1+b)G(1-b)]`, `b = θ/2π`, `|θ| < π` (`barnes_gamma_identity`), and `lem:VI` (`integral_wR`, `integral_wR_mul_rhoR`).  Not formalised: the complex
`g_θ` form of the first equality of `thm:BG` (only the real part, `re_gTheta`), the sharp `O(log)` bound for `Re ψ` inside the Barnes modules (they use a linear bound, which suffices; the sharper
`|Re ψ(½+is) - log|s|| ≤ 11/(8s²)` is `re_digamma_half_line` in `ComplexStirling`, not used by `Barnes*`), the Weierstrass product on all of `ℂ`, uniqueness of `G`, Gauss' series for `Re z ≤ 0`, and everything downstream (Barnes products,
entropy constants).
Phase-lattice summation of the same paper (`Lattice*`, umbrella `Lattice`, namespace `FormalResearch.Special.Lattice`): the Gauss-series branch
`argGammaHalf` of `arg Γ(½+is)` (analytic on `|Im s| < ½`, odd, real, derivative `Re ψ`, with elementary bounds on `Re ψ`; no Stirling), the abstract
lattice estimates for a calibrated phase (level counts and spacing, `latticeI_bound`, `latticeII_bound`), `lem:latticesum` (o) and (ii) for the
Gamma phase in paper form (`latticesum_gamma`), `lem:varcore` (i) and (ii) (`varcore_gamma`, `varcore_tail_gamma`, with `integral_hvar_gdens` from `lem:VI`), `lem:latticesum` (iii)
for the Gamma phase (`latticesum_gamma_iii`), `prop:offsetcore` (i) and (ii) for the Gamma phase without hypotheses on (iii) (`offsetcore_gamma`; the finite deduction is `offsetcore_i_of_iii`),
`lem:traceperturb` (`traceperturb`, via Lidskii) and `thm:tracecore` for the Gamma phase (`tracecore_gamma_opnorm`; namespace `FormalResearch.Special.TraceCore`, modules `Trace*`).  Not formalised:
`lem:latticesum` (i) for the Gamma phase as a standalone statement, the identification of `argGammaHalf` with the polar argument of `Γ`, and the verification of the hypotheses of
`thm:tracecore` in the cases (G), (H) of the paper (for (H), only the Airy-edge shape of the Hermite functions is formalised, see `HermiteAiry` below).
Complex Stirling formula and Binet's formulas (`ComplexStirling*`, umbrella `ComplexStirling`, namespace
`FormalResearch.Special.ComplexStirling`; Mathlib has no complex Stirling): Binet's formula for `log Γ` (DLMF §5.9(ii), (5.9.10_2)) and, by
differentiation, for `ψ` on `Re z > 0` (`digamma_eq_binet`, `binetLogGamma` with `exp (binetLogGamma z) = Γ z`, `log_Gamma_eq_binet` on the
reals, branch uniqueness among holomorphic logarithms of `Γ`), the explicit remainders on all of `Re z > 0`
`‖ψ(z) - (log z - 1/(2z))‖ ≤ 1/|z|²`, `‖ψ'(z) - 1/z - 1/(2z²)‖ ≤ (2/3)/|z|³`, `‖log Γ(z) - ((z-½)log z - z + ½ log 2π)‖ ≤ 2/|z|`
(non-sharp constants), the critical line `|Γ(½+is)|² = π/cosh πs`, `|Re ψ(½+is) - log|s|| ≤ 11/(8s²)`, `Im ψ(½+is) = (π/2) tanh πs`
and `Im log Γ(½+is) = s log|s| - s + O(1/|s|)`, and `|Γ(x+iy)|` in vertical strips with explicit remainder (`norm_Gamma_strip*`).  The
route is a Laplace transform of the Binet kernel, the difference equation and the identity theorem (no Euler–Maclaurin, no contour
rotation).  Imports `BarnesDigamma` (Gauss' series and convexity bounds) and the vendored `Interval.EulerMaclaurin.Gamma`
(Stirling's constant along `ℕ`); both are to be replaced before upstreaming.  Not formalised: the sharp constants and the Bernoulli
series (`1/12`-type), sectors `|arg z| > π/2` and `Re z ≤ 0`, the Weierstrass product form of `log Γ`, uniqueness of the branch among
merely continuous logarithms.
Hermite functions and their Airy edge (`Hermite*`, umbrellas `HermiteAiry` and `HermiteKappa`, namespace `FormalResearch.Special`; survey item T9, W1 `hermite.tex` `lem:PR`, case H): the orthonormal Hermite functions
`hermitePhi` (Mathlib's `Polynomial.hermite` over `ℝ`) with the exact three-term recurrence, ladder relations and parity (`hermitePsi_rec`, `hasDerivAt_hermitePhi_succ`, `hermitePhi_neg`),
`∫ φ_n² = 1` and the polynomial sup bound `φ_n² ≤ 2n+2` (`integral_hermitePhi_sq`, `abs_hermitePhi_le`), the reflected chain `Y_k = φ_{-k}(x)` as an *exact* simple-turn datum
`DunDatum` (`hermite_datum`, `hermite_row`: coefficient error `E = 0`), and the Plancherel–Rotach Airy edge (`hermite_airy_edge`): from `discrete_airy_full_unif`, on the macroscopic window `|(2n+1)/x² - 1| ≤ r`,
`φ_n(x) = κ g Ai(X) + μ g Bi(X)` with relative error `O(1/n)` in the Olver weights, `μ` exponentially small, absolute constants.  `HermiteKappa` (`HermiteKappa*`, 13 modules) adds
the Weber equation `φ_n'' = (x² - 2n - 1) φ_n` with the energy and an adiabatic invariant (`hasDerivAt_hkDer`, `hermite_weberData`), the **uniform envelope**
`φ_n(x)² √(|2n+1-x²| + (2n+1)^{1/3}) ≤ 12·10⁶` for all `n` and real `x` (`hermite_envelope`) and the size statement of W1 `lem:PR`(b) in product form (`hermite_PR_b`),
and the **order** of the Airy amplitude, `c ≤ κ² x^{1/3} ≤ C` (`|κ| ≍ S^{-1/12}`, `S = x²/2`; `hermite_kappa_order`, hence `κ ≠ 0`), with the Airy-edge chart data exported (`hermite_kappa_edge`).
Not formalised: the exact amplitude (numerically `κ = S^{-1/12}(1+o(1))`) and the sharp constants (the envelope's `12·10⁶` is crude, numerically `≈ 0.75`), uniqueness of `κ` in the Airy decomposition, the derivative bound and the oscillatory form with phase of `lem:PR`(a),
negative `x` and `x = 0` in the `κ` order theorem; the bulk expansion and phase for the Hermite chain (the generic discrete Liouville–Green layer `dlg_bulk_smooth` exists, see `DiscreteLg` below, but is not instantiated for it), closed form of the Langer coordinate,
Cramér's bound, orthogonality, the second solution of the Weber equation, the Mehler kernel, the Laguerre analogues.
Discrete Liouville–Green (Darboux) layer for Jacobi chains (`DiscreteLg*`, 10 modules, umbrella `DiscreteLg`, namespace `FormalResearch.Special`): the oscillatory bulk of a three-term recurrence with
smooth symmetric Jacobi coefficients and its matching to the Airy turn, first order with explicit `O(h)` error.  For a bulk datum `DlgData` (`A w² sin θ = 1`, `Θ' = θ`) the pair `w cos(Θ/h)`, `w sin(Θ/h)`
has row defect `O(h²)` and Casoratian `1 + O(h)` (`dlg_row_defect`, `dlg_cas_bound`), and the Airy-free variation-of-constants march gives, for every solution, `Y_k = R w(q_k)[cos(Θ(q_k)/h - φ₀) + O(h)]`
on any compact interior window (`dlg_bulk`, Cartesian form `dlg_bulk_cart`), with zero localisation in phase (`dlg_bulk_zero_bond`); for smooth `(A, u)` (`dlg_bulk_smooth`) and for the closed-form Hahn/Racah
chains on an arbitrary window `[c, d]` strictly inside the oscillatory region (`dlg_bulk_hahn`).  Airy matching (`dlg_airy_match`, `dlg_airy_match_smooth`, `dlg_airy_match_hahn`): from the Airy shape at two
sites, `Y_k = h^{1/6} π^{-1/2} w_k (κ cos χ_k + μ sin χ_k) + O(h^{1/6} h (|κ|+|μ|) w_k)`, `χ_k = (Θ_k - Θ*)/h + π/4`, i.e. phase offset exactly `π/4` and amplitude `h^{1/6}|κ|/√π`;
for the Hahn/Racah chains this is proved end to end from `airy_full_compose` and the Langer chart relations (`dlg_hahn_airy`, `dlgh_chart`).  Not formalised: second-order Liouville–Green; the value of `κ`
(for the `τ = +1` integer `3j` chain at a fixed rational shape `κ² = 2N^{1/3}(1+o(1))` is `hahn_chain_kappa_sharp`, but it is not composed with the matching here) so the amplitude `R` is known only up to `κ`; the oscillatory hypothesis `|hrU| < 1` on `[c₀, q_*)` is assumed, not derived from the
parameters; the other turning point / left edge, Bohr–Sommerfeld quantisation and node counting over the whole oscillatory interval; the continuum Wigner-`d` ODE form; constants are existential, not tracked in the parameters.
-/
