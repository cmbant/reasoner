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
`LangerJets`, `LangerCoordinate`); and the discrete Jacobi calculus for three-term recurrences (`DiscreteJacobiCalculus*`,
`DiscreteJacobiExtras*`: Lagrange/Casoratian identities, Green function, reduction of order, Volterra form, recessive
selection, final-value existence, hard-edge bridge, discrete Grönwall bounds).
-/
