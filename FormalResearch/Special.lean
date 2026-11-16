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

/-!
# Special functions: Jacobi polynomials

Jacobi polynomials `P_n^{(α,β)}` (DLMF 18): explicit-sum definition, differential equation,
derivative, reflection, three-term recurrence, orthogonality and norm (natural and real
parameters `α, β > -1`), zeros, Christoffel–Darboux, Rodrigues, and the Legendre, Chebyshev and
Gegenbauer special cases; the Mehler–Heine formula `n^{-α} P_n^{(α,β)}(cos(z/n)) → (z/2)^{-α} J_α(z)`
(`JacobiMehlerHeine`, `JacobiBessel`); the Laguerre recurrence of the hard-edge factor
(`LaguerreHardEdge`); the Airy function on `ℂ` and `ℝ`: definition by an absolutely convergent
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
Grönwall march (`AiryWindow*`: `discrete_airy_window`, Taylor remainders of `Ai` on `[-A0,-1]`); and the wiring layer that
composes all of these for a simple turn (`DiscreteAiryLimit*`): `discrete_airy_limit` (for one fixed smooth `u, A` with
`u(c₀) = 1`, `u'(c₀) > 0`, `A(c₀) > 0`: the exact recessive solution is `ψ = g·Ai(h^{-2/3}ζ)` within relative error `O(δ³)`
on `X ≥ 0` and within `O(δ³)` of the weight `W` on a bounded oscillatory window `X ≥ -A₀`, with the window positions exported,
and every solution with controlled end values is `κf + μf₂` with `μ` exponentially small), its bounded-window consequence
`dal_conclusion_window`, the closed-form Hahn / centred Racah instance `discrete_airy_hahn_racah(_window)`, the hard-edge
decay that discharges hypothesis (R) for the closed forms up to one normalisation `|Y_{k₁}| ≤ δ^{-p}` at an early forbidden-side
site (`DiscreteAiryLimitHyper*`: `hd_backward_decay`, `hr_hardedge_decay`, `discrete_airy_hahn_racah_hardedge(_window)`), and
the identification of the actual Wigner `3j`/`6j` chains (integer data) with the closed-form Hahn / centred Racah recurrences,
with the end conditions and the bound `|Ŷ| ≤ √N` from the Gauss weight, composed with the Airy limit
(`DiscreteAiryLimitChains*`: `hahn_class_chain`, `racah_class_chain`, `hahn_chain_airy`, `racah_chain_airy`).  Scope: one
fixed shape `(u, A, c₀)`, the recessive solution (not the non-recessive `Ai/Bi` pair), a bounded oscillatory window (not the
full oscillatory side); for the actual chains, integer data only (not half-integer), at lattice nodes `x_n = x` assumed to
exist (the congruence condition is not stated), the simple-turn data (and for Racah the branch `τ = +1` and `q_*`) being
hypotheses; `κ` is not identified (no Darboux matching, `κ ≠ 0` not proved), constants are existential (window constant
`e^{O(A₀²)}`); the input cited by the papers (GBVA, Geronimo) is still cited, not replaced.
-/
