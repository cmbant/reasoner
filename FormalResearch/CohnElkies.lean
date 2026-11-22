module

public import FormalResearch.CohnElkies.ResolventAverage
public import FormalResearch.CohnElkies.FourierL1Interp
public import FormalResearch.CohnElkies.CardinalTruncation
public import FormalResearch.CohnElkies.ClosedResolvent
public import FormalResearch.CohnElkies.StieltjesMixture
public import FormalResearch.CohnElkies.CardinalAsymptotics
public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.CohnElkies.MellinPhaseBounds
public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.CohnElkies.AiryNicholsonIntegral
public import FormalResearch.CohnElkies.AirySymbolWKB
public import FormalResearch.CohnElkies.CardinalPositiveAxis
public import FormalResearch.CohnElkies.CardinalSymbolBounds
public import FormalResearch.CohnElkies.AiryTwistedLaplace
public import FormalResearch.CohnElkies.OriginMellinAndS0
public import FormalResearch.CohnElkies.SaddleGeometry
public import FormalResearch.CohnElkies.LobeSaddleCore
public import FormalResearch.CohnElkies.LobeSaddleBounds
public import FormalResearch.CohnElkies.FiniteGaussianBase
public import FormalResearch.CohnElkies.FiniteDimensionCrossings
public import FormalResearch.CohnElkies.LaguerreJacobiSpectral
public import FormalResearch.CohnElkies.LaguerreSublinearLimit
public import FormalResearch.CohnElkies.TwoSaddleContraction
public import FormalResearch.CohnElkies.CohnElkiesRadius
public import FormalResearch.CohnElkies.CardinalFractionalSource
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor

/-!
# Cohn–Elkies / CFT Paper I elementary and toolkit lemmas (umbrella)

Formalised lemmas for CFT Paper I (`CFT/sign_uncertainty/paper/sign_uncertainty_core.tex` and components) in Mathlib
and the Airy library:

* `FormalResearch.CohnElkies.ResolventAverage`: scalar resolvent-product average identity `(CR.18)`.
* `FormalResearch.CohnElkies.FourierL1Interp`: `∫|f̂| ≤ 2π (‖f‖₂‖f'‖₂)^{1/2}` for Schwartz and `H¹(ℝ)` functions
  (Lemma T.5 / `(FG.3c)`), exact Fourier-multiplier representation `(FG.3b)`, and uniform `‖T_c f‖_∞` bound (Lemma FG.3).
* `FormalResearch.CohnElkies.CardinalTruncation`: `‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂)‖H_N − H‖₂` and uniform `H^∞`
  convergence `(GT.0)` for Airy-class functions.
* `FormalResearch.CohnElkies.ClosedResolvent`: Theorem CR.1 (closed diagonal Airy resolvent `(CR.2)`, Riccati equation,
  `(CR.4)` diagonal derivative step, `(CR.3)`, and removable case `z = a`).
* `FormalResearch.CohnElkies.StieltjesMixture`: Stieltjes mixture identities `(CR.19a)`, `(CR.8)`, `(CR.6b)`, `(CR.20)`,
  `(CR.7)`, and `(CR.9)`.
* `FormalResearch.CohnElkies.CardinalAsymptotics`: Proposition CR.3 asymptotics `(CR.11)–(CR.13)` and Theorem CR.4 Step 1
  `(CR.14a)–(CR.15)`.
* `FormalResearch.CohnElkies.MellinAiryToolkit`: Mellin–Airy toolkit Lemmas T.4(a)–(f) and T.3(1), T.3(3).
* `FormalResearch.CohnElkies.MellinPhaseBounds`: Mellin–Airy toolkit exact imaginary identity `T.3(3)`,
  Gaussian vertical-line bounds `T.3(4)–(5)`, and phase facts `T.4(e)` `(P1)–(P4)`.
* `FormalResearch.CohnElkies.MellinKernel`: Binet-remainder bridge (Lemma `T.1(a)`), Mellin-strip kernel
  identity (Lemma `T.2(1)` / `(e33)`), integrated tail `|R̃_5(iτ)|` (Lemma `T.4(b)` / `(e34)`), and combined
  `(P2)`/`(P4)` vertical bounds.
* `FormalResearch.CohnElkies.AiryNicholsonIntegral`: unconditional Nicholson integral error `E(x)` and
  phase correction `ϖ(x)` symbol/asymptotic bounds (Lemmas `W.3(a)` and `W.4(a)`).
* `FormalResearch.CohnElkies.AirySymbolWKB`: negative-axis Airy WKB representation, oscillation
  extraction, and `(CR.14)` all-order symbol decomposition (Lemmas `W.2(b)–(c)`, `W.3(b)`, `W.4(b)`,
  Props `W.5`, `W.6`).
* `FormalResearch.CohnElkies.CardinalPositiveAxis`: Bessel `K_{1/3}/K_{2/3}` model (`W.1`), Euler
  derivative bounds, and positive-axis `(CR.16)` bounds for `F(t)`.
* `FormalResearch.CohnElkies.CardinalSymbolBounds`: Theorem `CR.4` Steps 2–4 (`(CR.17)`, `(CR.21)`
  uniformly in probability measure `Λ`, and `theorem_CR4_symbol_decomp`).
* `FormalResearch.CohnElkies.AiryTwistedLaplace`: real-axis twisted Airy Laplace asymptotic (`ce_rate.tex`
  Lemma `P.1(1)` / `(cel:3.2)`).
* `FormalResearch.CohnElkies.OriginMellinAndS0`: positive source `S₀` two-sided floor (`P.1(2)`) and
  origin Mellin kernel bounds (`ce_rate.tex` Lemma `P.2(1)` / `(cel:4.6)`).
* `FormalResearch.CohnElkies.SaddleGeometry`: elementary `cos²` averaging (`P.5`), strip function
  reflection, saddle scales, and local vertical curvature (`ce_rate.tex` Lemma `P.3(2)–(3)`).
* `FormalResearch.CohnElkies.LobeSaddleCore`: vertical phase derivative, `LobeSaddleAmp`,
  saddle-line integrability, and inner saddle window error bound (`ce_rate.tex` Prop `P.4` core).
* `FormalResearch.CohnElkies.LobeSaddleBounds`: outer tail & additional damping estimates,
  uniform lobe saddle asymptotic (`ce_rate.tex` Prop `P.4`, Remark `P.4a`), and `lobeSaddleAmp_nonvacuous`.
* `FormalResearch.CohnElkies.FiniteGaussianBase`: Cohn–Elkies admissibility, radial Schwartz
  Gaussian Fourier transforms, and quadratic Gaussian Theorem `E.1` (`ce_finite_bounds.tex`).
* `FormalResearch.CohnElkies.FiniteDimensionCrossings`: Stirling–Robbins and dyadic log bounds,
  quadratic dimension crossings (`E.2`), and cubic Laguerre Gaussian bounds (`E.2'`).
* `FormalResearch.CohnElkies.LaguerreJacobiSpectral`: Laguerre orthogonal basis `laguerreHat`,
  three-term recurrence, Hermitian Jacobi matrix, and Rayleigh spectral lower bound.
* `FormalResearch.CohnElkies.LaguerreSublinearLimit`: `[0, ∞)`-SOS factorization, exact finite
  lower bound, sublinear-degree limitation (`E.3a`), and `κ_Gauss` attainment.
* `FormalResearch.CohnElkies.TwoSaddleContraction`: Airy–Curie–Weiss two-saddle contraction (`O.11aw`),
  infinite Airy-cardinal identity and `L²(ℝ)` Parseval (`O.11f`), `PF.3` positive-argument kernel bound,
  and `PF.5` worst-phase & interval margin (`ce_o1_route.tex`, `ce_physical_log_far.tex`).
* `FormalResearch.CohnElkies.CohnElkiesRadius`: Cohn–Elkies density-volume Stirling asymptotic (`7.12a`),
  equivalence of `L¹` and Schwartz infima (`7.12`), and conditional Airy-order radius gluing (`ce_radius.tex`).
* `FormalResearch.CohnElkies.CardinalFractionalSource`: balanced/unbalanced fractional Stieltjes cardinal
  source, closed-form `J_{2,p}`, exact mass `∫ P_h = M, ∫ Q_h = 0`, `D_h` Airy-zero asymptotic, and `η̂_h`
  bound (`ce_o1_route.tex` Lemma `O.11h`).
* `FormalResearch.CohnElkies.PreEdgeAndSplineFloor`: uniform B-spline averaging floor (`O.0`, `O.1`),
  Airy Riccati monotonicity (`PE.1`), two-scale Dirichlet floor (`cepe:dirichlet-floor`), and `B_c^*`
  Hölder bound (`cepe:PE3a`) (`u1c_o1_upper.tex`, `ce_o1_pre_edge.tex`).

This umbrella is deliberately not imported by `FormalResearch.lean`.
-/
