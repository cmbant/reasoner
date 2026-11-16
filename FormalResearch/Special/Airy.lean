module

public import FormalResearch.Special.AiryKernel
public import FormalResearch.Special.AiryDef
public import FormalResearch.Special.AiryReal
public import FormalResearch.Special.AiryBound
public import FormalResearch.Special.AiryEquation
public import FormalResearch.Special.AiryIdentities
public import FormalResearch.Special.AiryPositive
public import FormalResearch.Special.AiryZeros
public import FormalResearch.Special.AiryRotation
public import FormalResearch.Special.AiryValues
public import FormalResearch.Special.AiryTaylor
public import FormalResearch.Special.AiryFourier
public import FormalResearch.Special.AiryKernelOpOperator
public import FormalResearch.Special.AiryKernelOpComplex
public import FormalResearch.Special.AiryKernelOpSharp
public import FormalResearch.Special.AiryBridge
public import FormalResearch.Special.AiryNodes
public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryEnvelopeReal
public import FormalResearch.Special.AiryAbel
public import FormalResearch.Special.AiryIntegralArc
public import FormalResearch.Special.AiryIntegral
public import FormalResearch.Special.AiryHypergeometric
public import FormalResearch.Special.AiryKernelOpL2
public import FormalResearch.Special.AiryGram
public import FormalResearch.Special.AiryEnvCalculus
public import FormalResearch.Special.AiryAsymSector
public import FormalResearch.Special.AiryAsymNegComplex
public import FormalResearch.Special.AiryGoodCircles
public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryAsymSaddle
public import FormalResearch.Special.AiryAsymNeg
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.AiryAsymPos
public import FormalResearch.Special.AiryAsymZeros
public import FormalResearch.Special.AiryBiReal
public import FormalResearch.Special.AiryAsymBiNeg
public import FormalResearch.Special.AiryAsymBiPos
public import FormalResearch.Special.AiryAsymChiAux
public import FormalResearch.Special.AiryAsymChi
public import FormalResearch.Special.AiryBiMono
public import FormalResearch.Special.AiryBiNeg
public import FormalResearch.Special.AiryBiEnvelope
public import FormalResearch.Special.AiryOlver
public import FormalResearch.Special.AiryOlverBounds
public import FormalResearch.Special.AiryGammaBounds
public import FormalResearch.Special.AiryZeroTaylor
public import FormalResearch.Special.AiryZeroGap
public import FormalResearch.Special.AiryFirstZeros
public import FormalResearch.Special.AiryZeroOrder
public import FormalResearch.Special.AiryZeroLabel
public import FormalResearch.Special.AiryZeroSpacing
public import FormalResearch.Special.AiryZeroLemmaZ
public import FormalResearch.Special.AiryZeroSecondOrderSaddle
public import FormalResearch.Special.AiryZeroSecondOrderChi
public import FormalResearch.Special.AiryZeroSecondOrderPhase
public import FormalResearch.Special.AiryZeroSecondOrder
public import FormalResearch.Special.AiryPruferAsym
public import FormalResearch.Special.AiryClarkMid
public import FormalResearch.Special.AiryWt
public import FormalResearch.Special.AiryShift
public import FormalResearch.Special.AiryShiftTaylor
public import FormalResearch.Special.AiryCftCircle
public import FormalResearch.Special.AiryCftZeros
public import FormalResearch.Special.AiryCftMittagLeffler
public import FormalResearch.Special.AiryCftResidue
public import FormalResearch.Special.AiryCftDefect
public import FormalResearch.Special.AiryCftWeights
public import FormalResearch.Special.AiryCftQuadrature

/-!
# The Airy function: aggregate and design note

Mathlib has no Airy function.  Here `Ai(z) = (1/2π) ∫_ℝ exp((1+is)³/3 - z(1+is)) ds` is defined on `ℂ`
(`airyAiC`; absolutely convergent, Gaussian decay in `s`), with `airyAi : ℝ → ℝ` its real restriction.
Modules: `AiryKernel` (kernel, majorants, integration by parts in `s`), `AiryDef` (entire, `Ai'' = z Ai`,
independence of the abscissa `c > 0` by differentiating in `c`, derivatives are the moments),
`AiryReal` (real on `ℝ`, smooth), `AiryBound` (explicit decay on `(0,∞)`), `AiryEquation` (identities for any
solution of `y'' = x y`, ODE uniqueness; independent of the definition), `AiryIdentities` (`∫_x^∞ Ai²`, kernel
limits), `AiryPositive` (two-sided bounds, `Ai > 0`, `Ai' < 0` on `[0,∞)`), `AiryZeros` (zeros are real and
negative), `AiryRotation` (`Ai(z) + ω Ai(ωz) + ω² Ai(ω²z) = 0`, `Bi`, Wronskian constant), `AiryValues`
(`Ai(0)`, `Ai'(0)`, `Bi(0)`, `Bi'(0)` in terms of `Γ(1/3), Γ(2/3)`; `W(Ai, Bi) = 1/π`; contour rotation to
the rays `arg t = ±π/3`), `AiryTaylor` (`Ai = Ai(0) F + Ai'(0) G` with the explicit entire series `F, G`),
`AiryFourier` (`∫_ℝ Ai(x) e^{ax} dx = e^{a³/3}` for `Re a > 0`; Abel-regularised Fourier transform),
`AiryKernelOp{Formula,Bounds,Operator,Complex}` (the Airy kernel as a Gram integral `∫_0^∞ Ai(x+t)Ai(y+t)dt` for real and
complex `x,y`, diagonal bounds, `∫_u^∞ K(s,s)ds`, Hilbert–Schmidt/trace finiteness and positivity of the quadratic form),
`AiryEnvelope*` (free-parameter bound for every `c > 0`; the complex envelope `|Ai(z)| ≲ (1+|z|)^{-1/4} e^{-(2/3) Re z^{3/2}}`
on all of `ℂ`, the same for `Ai'`, order `3/2`; `Ai > 0` on `[-1, ∞)` and the two-sided real-axis envelope there),
`AiryIntegral*`, `AiryAbel` (`∫_0^∞ Ai = 1/3`, `∫_{-T}^0 Ai → 2/3`, `∫_{-S}^T Ai → 1` by an entire primitive, the rotation identity and
an Abelian theorem), `AiryHypergeometric` (`Ai` through Mathlib's regularized `₀F₁`), `AiryKernelOpL2` (`K_u` on `L²(u,∞)` at function
level: `∫(K_u f)² ≤ N_Ai(u)² ∫f²`, symmetric, positive), `AiryGram` (Abel-regularised orthogonality of translates),
`AiryEnvCalculus`, `AiryAsymSector`, `AiryAsymNegComplex`, `AiryGoodCircles`, `AiryRatioBounds` (envelope calculus `e(u+τ) ≤ e(u)e^{-2τ Re√u}`,
sector asymptotics with relative remainder, `Ai` near the negative axis for complex phase, zero-free good circles with
`‖Ai‖² ≥ c(1+r)^{-1/2} e` for the pure-`Ai` case of (E2), and `|(Bi ∓ iAi)/Ai| e ≤ C` there),
`AiryAsym{Saddle,Neg,Real,Pos,Zeros}` (exact
saddle-point formula `Ai(w²) = (e^{-(2/3)w³}/2π) ∫ exp(-w s² - i s³/3) ds`, `Re w > 0`, with the second-order
estimate; hence `Ai, Ai', Bi` on the negative axis with explicit `O(y^{-3/2})` relative error, the amplitude
`Ai² + Bi²` and the kernel diagonal `K(-y,-y) = √y/π (1+O(y^{-3/2}))`, positive-axis asymptotics of `Ai, Ai'`, and the
location of the zeros `y ≥ 4`), then
`AiryBiReal` (`Bi'` on `ℝ`, `Bi'' = x Bi`, the real Wronskian), `AiryAsymBi{Neg,Pos}` (`Bi'` on the negative axis, `Bi`, `Bi'`
on the positive axis, first terms with explicit remainders), `AiryAsymChi{,Aux}` (`χ = Ai + iBi` on the negative axis with the
`u_1 = 5/72` term: `Ai`, `Bi` to order `u_1`; the `u_2` term for `Ai`, `Bi` is in `AiryZeroSecondOrder{Saddle,Chi}`), `AiryBi{Mono,Neg,Envelope}` (`Bi/Ai` increasing, `Bi > 0` and `Bi' > 0` on
`[-11/10, ∞)`, two-sided envelope of `Bi` on `[-1, ∞)`), `AiryOlver{,Bounds}` (the DLMF 9.8 modulus `Ai² + Bi²`, Olver's weights
`E`, `M` and a convenient majorant `airyDerivWeightN` of the derivatives, which is *not* Olver's `N`, with two-sided bounds);
the ordered zeros `a_n` of `Ai`: `AiryGammaBounds`, `AiryZeroTaylor`, `AiryFirstZeros` (rational enclosures of `Γ(1/3)`, `Γ(2/3)`,
`Ai(0)`, `Ai'(0)`, the sign change of `Ai` at `-2.33`, `-2.35`, and `a_1, a_2`), `AiryZeroGap` (Prüfer rate, spacing of zeros),
`AiryZeroOrder` (`airyZero n`), `AiryZeroLabel` (the phase theorem `|(2/3)|a_n|^{3/2} - (n-1/4)π| ≤ (2/5)|a_n|^{-3/2}`, DLMF 9.9.6),
`AiryZeroSpacing` (`|a_n| ≍ n^{2/3}`, gaps `≍ n^{-1/3}`), `AiryZeroLemmaZ` (`a_n = -((3π/2)(n-1/4))^{2/3} + O(n^{-4/3})`),
`AiryZeroSecondOrder{Saddle,Chi,Phase,}` (the second order DLMF 9.9.18: `|a_n + t^{2/3}(1 + 5/(48t²))| ≤ 2t^{-10/3}`,
`t = (3π/2)(n-1/4)`, via the saddle integral and `Ai`, `Bi` on the negative axis to relative order `r^{-9}` and the phase
`|(2/3)r³ - (n-1/4)π - 5/(48r³)| ≤ (11/10)r^{-9}`; constants not sharp),
`AiryPruferAsym` (the Prüfer angle of `Ai`, zeros of `Ai'`), `AiryClarkMid` (one zero of `Ai'` per gap, asymptotically the
midpoint); and the Airy side of the discrete-to-Airy limit: `AiryWt` (an explicit envelope weight `(2+|X|)^{-1/4} e^{-ξ}` with
local constancy and lattice sums), `AiryShift` (the shift identity `y(X+s) = y(X) C + y'(X) S`), `AiryShiftTaylor` (Taylor
expansions of `Ai`, `C`, `S` against the weight); and the CFT consequences of the zeros of `Ai` (`AiryCft*`: see the design
note).  The Langer coordinate (`Langer*`), the discrete Jacobi calculus
(`DiscreteJacobi*`) and the discrete-to-Airy comparison built on it (`AiryParametrix*`, `AiryRecessive*`, `AiryWindow*`, `DiscreteAiryLimit*`)
are separate modules of `FormalResearch.Special`, not imported by this aggregate.  (Overlapping Gamma enclosures: `AiryBiNeg` and
`AiryGammaBounds` each carry their own, with different constants.)

**Not formalised:** the full asymptotic series (the `AiryAsym*` files give the first term, or `u_1` in `AiryAsymChi`, with explicit
remainder; `AiryZeroSecondOrder*` add `u_2` for `Ai`, `Bi` on the negative axis, not `u_3` and higher terms; `Ai'`, `Bi'`, `χ'`
to order `v_1` only to first order); the `-(5/36)t^{-4}` coefficient of the zeros' expansion and the zeros of `Ai'`
(DLMF 9.9.19), the second order of DLMF 9.9.18 itself being proved with non-sharp constants, and sharp constants anywhere; the asymptotics of the general Clark nodes `z_n(α)`, `α ≢ 0, π/2`
(existence and uniqueness are `airy_node_exists_unique`); Olver's own `N` and the value of the crossing point `c = -0.366…`
(`airyCross > -1`); Olver-type uniform expansions; the Mellin moments `∫_0^∞ x^{s-1} Ai`, `Ai ∉ L¹(-∞,0)`; the `Lp`-level
operator `K_u`; the `Ai'` and `P Ai + Q Ai'` versions of the good-circle bound (E2) and hence of the residue-defect formula, Clark-Airy
summation for `ψ_α`, and Theorem Q for `ν ∈ [-1, 1/2]` (`AiryCftQuadrature`); the product form of `Ai'` and `Bi`, and
the converse of Hadamard's theorem (`FormalResearch.Complex`); the first zero of `Bi` and `Bi > 0`
beyond `-11/10`; the open parts of the discrete-to-Airy chain: the Darboux normalisation `κ` and `κ ≠ 0` (also the single
normalisation `|Y_{k₁}| ≤ δ^{-p}` for the closed-form chains), the non-recessive `Ai/Bi` pair and the full oscillatory side,
uniformity over families (and the existence of lattice nodes), half-integer chain data, the derivation of the Racah `q_*` and
the `τ = -1` branch, explicit constants, and analyticity of the Langer coordinate (see the design note).

Design note: what the Airy connection of `Weyl/P3` (`thm:general-rank-airy`) and the free-fermion edge
(`Weyl/free_fermion`, `thm:edge`) need next, and what is now reachable.
* *Forbidden-side/recessive input*: `Ai > 0`, monotone, `|Ai|, |Ai'|` explicit decay, `Ai'/Ai < 0`:
  done (`AiryPositive`, `AiryBound`).  Intrinsic boundedness of the discrete solution beyond the turn
  compares with this recessive solution: reachable now (Sturm-type comparison for the recurrence).
* *Canonical `Ai/Bi` basis and variation of constants* (Green function of the Airy-form branch): `Bi`, `Bi'' = zBi`
  and the Wronskian `W(Ai, Bi) = 1/π` are in place (`AiryValues`: `Ai(0)Ai'(0) = -1/(2√3 π)` by a contour
  rotation to the rays `arg t = ±π/3`, proved by a derivative-in-the-ray-direction argument as for `airyMom_indep`).
* *Olver modulus/weight `M, E` and the uniform bracket `Ai + N^{-4/3}ϖ Ai' + O(N^{-2})`*: the weights `E`, `M` of Olver and
  the DLMF 9.8 modulus are in place on the real axis (`AiryOlver`, `AiryOlverBounds`, with `Bi` on all of `ℝ` via
  `AiryAsymBi*`, `AiryBi*`), as is the explicit stand-in `airyWt` for `M/E` (`AiryWt`); the uniform-in-`x` bracket with
  the `N^{-4/3}` correction (Olver's uniform expansions) remains open.
* *Discrete recurrence → Airy ODE limit*: Gronwall/uniqueness (`airy_unique_real`), the wronskian/energy identities, then, in
  `FormalResearch.Special` and not in this aggregate: M1/M1b the generic recurrence calculus (`DiscreteJacobi*`: Casoratian,
  Green function, reduction of order, final-value existence, hard-edge bridge, discrete Grönwall bounds); M2 the Airy shift
  identity and Taylor expansions at the turn (`AiryShift`, `AiryShiftTaylor`, mesoscopic hypothesis `|s|√(1+|X|) ≤ Λ`); M3 the
  Langer coordinate (`Langer*`); M4 the parametrix defect in window form (`airyParametrix_defect`: `K h²(1+|X|)³ airyWt`,
  with the amplitude relation `g²Aζ'Sh(ζζ'²) = 1` *assumed*); M7a (`AiryParametrixLanger`) the amplitude relation
  `g²Aζ'Sh(ζζ'²) = 1` and `Ch(ζζ'²) = u` *proved* for M3's own `ζ, g` near a simple turn, with the combined window-form
  defect; M7b (`AiryParametrixUniform*`) the *uniform* defect `≤ K h² airyWt X` with no `(1+|X|)³`, for every real `X`
  (the turn neighbourhood `X ~ h^{-2/3}` included), and its lattice and relative forms `≤ K h² |ψ_k|` (under
  `-1 ≤ h^{-2/3}ζ`); M5 the recessive discrete solution and second solution under the relative defect hypothesis
  `|jac ψ| ≤ C₀h²ψ` (`AiryRecessive*`); M6 the bounded oscillatory window by a discrete Grönwall march
  (`discrete_airy_window`, asymptotic regime `δ ≤ δ₀`, `δ³ = h`; the constant is pessimistic, `e^{O(A0²)}`); and the wiring
  layer (`DiscreteAiryLimit*`): `discrete_airy_limit`, an abstract simple-turn theorem composing M1–M7 (for one fixed
  `u ∈ C³`, `A ∈ C²` with `u(c₀) = 1`, `u'(c₀) > 0`, `A(c₀) > 0`: the exact recessive solution is `g·Ai(h^{-2/3}ζ)` within
  `O(δ³)` relative error on `X ≥ 0` and within `O(δ³)W` on a bounded oscillatory window `X ≥ -A₀`, the window positions
  `X_J ≲ -A₀`, `X_m ≈ 0` being exported, and every solution with controlled end values is `κf + μf₂` with `μ` exponentially
  small), `dal_conclusion_window` (its bounded-window form `Y = κg(Ai + O(h))`, from a polynomial bound `|Y_N|, |Y_{N+1}| ≤
  δ^{-p}`, hypothesis (R), on the forbidden-end values), and the closed-form Hahn / centred Racah instance
  `discrete_airy_hahn_racah(_window)` (simple-turn data from `1 - τx > 0`, `O(h²)` comparison of the closed-form `A_k, c_k`).
  This covers the recessive solution with relative `O(h)` error and a bounded oscillatory window for one fixed `(u, A, c₀)`
  under (R); it does **not** cover the non-recessive canonical `Ai/Bi` pair, the oscillatory side beyond the bounded window,
  uniformity over families of shapes, or the identification of `κ` (Darboux matching) or `κ ≠ 0`; constants are existential
  (window constant `e^{O(A0²)}`), and the input cited by the papers (GBVA, Geronimo) is still cited, not replaced.
  Two further pieces now close the (R) and chain-identification gaps for the closed forms.  Hard-edge decay
  (`DiscreteAiryLimitHyper*`): `hd_backward_decay` (abstract monotone decay `|Y_k| ≤ |Y_{j-1}|` to a hard edge `A_{N+1} = 0`),
  `hr_hardedge_decay` (for the closed-form Hahn / centred Racah rows, via `exact_hyperbolicity_hahn_racah` row by row) and
  `discrete_airy_hahn_racah_hardedge(_window)`: (R) is derived from the hard edge up to **one normalisation**
  `|Y_{k₁}| ≤ δ^{-p}` at an early forbidden-side site `k₁` (the decay runs from `k₁` to the edge, so a bound at the end of the
  chain gives nothing there).  Actual chains (`DiscreteAiryLimitChains*`): for integer data the actual Wigner `3j` and `6j`
  natural-gauge chains `Ŷ_k = √(2k+1)Φ_k` satisfy the closed-form Hahn / centred Racah recurrences for every `k ≥ 1`
  (`hahn_class_chain`, `racah_class_chain`; gauge change of the paper's exact rank recurrences), with the support and end
  conditions (`A_{k_max+1} = 0`) and `|Ŷ| ≤ √N` resp. `√(4AB/2C)` from one term of the Gauss weight; `hahn_chain_airy` and
  `racah_chain_airy` compose these with `discrete_airy_hahn_racah`, so (R) is proved, not assumed, for the actual chains at
  integer data (Hahn at a lattice node `x_n = x`, e.g. `M = σ = 0`, `x = 1/2`, `N = 4t+2`, `n = 3t+1`; the existence of
  nodes is not stated in general; Racah on the branch `τ = +1` with the turn data `q_*` taken as hypotheses).  Open: `κ` and
  `κ ≠ 0` (Darboux), the non-recessive `Ai/Bi` pair, the full oscillatory side, uniformity over families, half-integer chain
  data (the chain lives on the shifted lattice), the derivation of the Racah `q_*` and the `τ = -1` branch, explicit
  constants, and analyticity of `ζ`.
* *CFT consequences of the Airy zeros* (`AiryCft*`; direct route by good circles, no Hadamard theory).  Generic
  complex analysis (`AiryCftCircle`: for an entire `f` with simple zeros `c_i` in a disc, `f = Π(w - c_i) φ` with
  `φ` zero-free, the circle formulas for `f'/f` and its derivative as Cauchy integrals with error bounds;
  `AiryCftResidue`: `∮ H/f = 2πi Σ H(c_i)/f'(c_i)`, a residue formula for simple poles, which Mathlib lacks); the zeros of
  `Ai` in `ℂ` are exactly the `a_n`, simple, with every radius splitting the list, and `‖Ai'/Ai‖ ≤ 45√(1+r)` on a good
  circle (`AiryCftZeros`); the Mittag-Leffler expansion `Ai'(z)/Ai(z) = Ai'(0)/Ai(0) + Σ(1/(z-a_n) + 1/a_n)` and the sum
  rules `Σ(z-a_n)^{-2} = (Ai'/Ai)² - z`, `Σ a_n^{-2} = (Ai'(0)/Ai(0))²` with its closed form
  (`AiryCftMittagLeffler`); Theorem D, the residue-defect formula for entire `f` with `Bi(a_n) = -1/(πAi'(a_n))`:
  `‖Σ_{n ≤ N} f(a_n)/Ai'(a_n)² - ∫_{-R}^R f‖ ≤ πRM` if `‖f R_±‖ ≤ M` on the half circles (`AiryCftDefect`); and
  Corollary D1, the quadrature `∫_ℝ f = Σ_{n ≥ 1} f(a_n)/Ai'(a_n)²` for `f` entire with `‖f(u)‖ ≤ C(1+|u|)^ν e(u)` on
  all of `ℂ` and `ν < -1` (`AiryCftWeights`, `AiryCftQuadrature`).  Honest scope: `f` is entire with the bound on all of
  `ℂ`; that the class is non-empty and useful (e.g. smearings of `Ai`) is checked only mathematically/numerically in the
  module docstrings, not in Lean; the constants `45`, `30√π` are not sharp.  Open: `Ai'/(P Ai + Q Ai')` good circles (the
  derivative analogue of `AiryAsymNegComplex`), Clark summation for `ψ_α` and Theorem D for `P Ai + Q Ai'`, Theorem Q for
  `ν ∈ [-1, 1/2]` (Hardy-space unfolding, Fejér-Riesz), `f` holomorphic only near the closed disc.
* *Hadamard factorization* (`FormalResearch.Complex`, `Hadamard*`, namespace `FormalResearch.Hadamard`; a separate aggregate,
  not imported by this one, since only `HadamardAiry` uses the Airy modules and nothing here uses it): the general
  theorem for entire functions of finite order, `f(z) = c z^m e^{P(z)} Π E_p(z/a_i)` with `deg P ≤ p` for
  `|f| ≤ C exp(C|z|^σ)`, `σ < p+1` (`Hadamard.hadamard`, `hadamard_floor`, `hadamard_exists`: Weierstrass products,
  Jensen counting of zeros, Blaschke/Borel–Carathéodory estimates and a derivative route replacing lower bounds on
  circles), and its application to `Ai` (order `3/2`, genus one): `Ai(z) = Ai(0) exp((Ai'(0)/Ai(0)) z) Π(1 - z/a_n)e^{z/a_n}`
  (`Hadamard.airyAiC_hadamard`).  Mathlib has Jensen's formula, Borel–Carathéodory and canonical decompositions but no
  Hadamard factorization theorem, so this is upstreamable in principle.  Not formalised: the converse (finite genus implies
  finite order), order = convergence exponent, lower bounds on canonical products, the closed value of `Ai'(0)/Ai(0)`
  inside the product form, the products for `Ai'` and `Bi`.  The Mittag-Leffler expansion above is the logarithmic
  derivative of this product, proved independently.
* *Free-fermion edge*: the Airy kernel `K(x,y)`, `K(x,x) = Ai'² - x Ai²`, `(∂_x + ∂_y)K = -Ai(x)Ai(y)` and
  `∫_x^∞ Ai² = K(x,x)` are in place, and `K(x,y) = ∫_0^∞ Ai(x+s)Ai(y+s) ds` (hence positivity of `K`) is
  `airyKer_eq_integral` (real `x,y`) and `airyKerC_eq_integral` (complex `x,y`) in `AiryKernelOp*`.
-/

