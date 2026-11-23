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
public import FormalResearch.CohnElkies.MellinEdgeValues
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
public import FormalResearch.CohnElkies.AiryGaussianTransform
public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.CohnElkies.CardinalSignRegions
public import FormalResearch.CohnElkies.MovingDiagonalSource
public import FormalResearch.CohnElkies.MellinMainKernel
public import FormalResearch.CohnElkies.PhysicalAndFarTransfer
public import FormalResearch.CohnElkies.CoherentSectorialLimit
public import FormalResearch.CohnElkies.DualPhaseAndO3
public import FormalResearch.CohnElkies.CancelledSymbolAndLaplace
public import FormalResearch.CohnElkies.AirySeedSymbols
public import FormalResearch.CohnElkies.CubicNormalFormContraction
public import FormalResearch.CohnElkies.ComplexEdgePhase
public import FormalResearch.CohnElkies.CubicNormalFormBridge
public import FormalResearch.CohnElkies.CubicNormalFormH
public import FormalResearch.CohnElkies.MellinLiftIntegrals
public import FormalResearch.CohnElkies.AiryWindowInversion
public import FormalResearch.CohnElkies.FresnelBranch
public import FormalResearch.CohnElkies.PieceCDecomposition
public import FormalResearch.CohnElkies.PieceCPhase
public import FormalResearch.CohnElkies.PreEdgeCriterion
public import FormalResearch.CohnElkies.AirySymbolTransfer

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
* `FormalResearch.CohnElkies.MellinEdgeValues`: left-edge value `Re ℋ(iτ)` of the strip function and the
  Γ-ratio bound on the edge (`gt:7.4(2)` inputs).
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
* `FormalResearch.CohnElkies.AiryGaussianTransform`: fractional Stieltjes measure `dμ_p`, `Z_p`, `𝒢_p`,
  `B_p` (`O.11j`, `O.11n`), reproducing identity & exact Airy-square Gaussian transform (`(ceo:O11n.2)`),
  and uniform vertical-line bound (`(ceo:O11n.11)` `j = 0`).
* `FormalResearch.CohnElkies.AirySeedFloors`: positive Airy seed `S_b` & rational–Airy `(e22)`–`(e23)`
  floor (`U.4a`), Hermite–Biehler mass-prescribed seed family `F_δ` (`lem:hb-seed-mass` with `N = Ai`
  non-vacuity witness & smoothing-gain corollary), and small-`L` cubic normal-form scale `κ₀(L)` +
  real-axis derivative floor (`O.4` `(1)` & `(3)`).
* `FormalResearch.CohnElkies.CardinalSignRegions`: exact Stieltjes resolvent `H_{s,h}`, `J(w)` asymptotic,
  and physical sign `Q_h > 0` across all three regions covering `u < a₁` (`O.11p`) and on the full
  moving far half-line `x ≥ t₀ / h` (`O.11j`, `(ceo:O11j.2)`, `(ceo:O11j.5)`–`(ceo:O11j.10)`).
* `FormalResearch.CohnElkies.MovingDiagonalSource`: Dirichlet vector bounds (`O.11x`), positive moving diagonal
  complement `𝒮_h` (`O.11w`), and two-scale joint Airy source `S_c, F_c^{(0)}, F_c` (`O.11y` `(1)–(4)`).
* `FormalResearch.CohnElkies.MellinMainKernel`: B-spline multipliers `bsplineE1`/`bsplineMult`/`bsplineImag`,
  exact Mellin main-edge kernel `O.11ae` (`H²`, `L¹ = O(c^{-1/2})`, `y⁻² c⁻²` decay, Fubini bridge),
  and Lemma `GT.2b(1)–(2)` rank-`∞` Gaussian derivative bounds (`β ∈ {0, 1}` and `(ceo:O11n.11)`).
* `FormalResearch.CohnElkies.PhysicalAndFarTransfer`: unconditional Lemma `FG.3` (`‖T_c f‖_∞` multiplier bound),
  unconditional `PF.T(1)` omitted-region bound, `GT.3b` far-Fourier transfer (with the pruned
  `MacroscopicTransferPackage`), and the `GT.4` exact leading tip offset. The Route I consumers
  `PF.2`, `PF.5` and the `GT4CoverageBands` package were removed.
* `FormalResearch.CohnElkies.CoherentSectorialLimit`: unconditional Lemma `O.11n` Dirichlet resolvent `(ceo:O11n.8)`,
  Stieltjes mixture `(ceo:O11n.10)`, uniform `L^∞` bounds `(ceo:O11n.4)`/`(ceo:O11n.9)`/`(ceo:O11n.11)`,
  boundary-layer limit `(ceo:O11n.3)`, complex sectorial & `C²` limits `(ceo:O11n.5)–(ceo:O11n.6)`, and `PE.1`
  real-axis Gaussian lower bound.
* `FormalResearch.CohnElkies.DualPhaseAndO3`: unconditional Lemma `O.2` reflected-line (`2^{r+5/2} r!`) &
  weighted imaginary-axis `(e29)` bounds, `bsplineMult_binomial_eq`, unconditional `O.3(1)` oscillatory phase
  bound (`dual_phase_oscillatory_bound`), `GT.2b(3)` / `(cegt:GT3a)` (`gt2b_dual_integral_general`), and `(e3)`
  (`o3_dual_bound`).
* `FormalResearch.CohnElkies.CancelledSymbolAndLaplace`: unconditional Gaussian transforms & Gaussian-IBP `y^{-9/2}`
  expansions (`ceF1`, `ceG1`, `ceG1Deriv`), Lemma `O.11c` (`(ceo:O11c.1)–(2)`), `P.1(2)`/`U.2` RHP and dual-line
  bounds for `ceS0`/`ceSb`, and unconditional `twoScaleQ0_real_laplace_bound`.
* `FormalResearch.CohnElkies.AirySeedSymbols`: `U.2` for the one-level seeds `a f₁ + b g₁ + c g₁'` (`HasU2`, closed under
  linear combinations; RHP and dual-line bounds; the `m₀ = 1` Hermite–Biehler seed).
* `FormalResearch.CohnElkies.CubicNormalFormContraction`: `O.4(2)` fixed-point step (`o4G`, `o4_fixed_point`): Banach
  contraction on `D(0, 0.22)` for an abstract holomorphic `F` under the named hypothesis `‖F‖ ≤ 0.13` on `D(0, 0.25)`.
* `FormalResearch.CohnElkies.ComplexEdgePhase`: holomorphic edge phase `Φ_L` on `D(0, 1)` (`stripQ`, `differentiableOn_stripG`,
  `edgePrim`, `edgePhiC`: derivative, oddness, agreement with the real `edgePhi`).
* `FormalResearch.CohnElkies.CubicNormalFormBridge`: `O.4(2)` normal form `τ(θ)` from the fixed point (`removable_finite`,
  `o4_quotient_ext`, `o4_normal_form`), under the named hypothesis `O4QuotientBound` (`M_F ≤ 0.13`).
* `FormalResearch.CohnElkies.CubicNormalFormH`: `O.4(2)` remainder `H(θ) = θ⁻³(τ(θ) - κ₀θ)` extended holomorphically to `D(0, 0.22)` with `|H| ≤ 1/4`
  (`even_quotient_differentiableOn`, `even_quotient_bound`, `O4NormalForm.H_bound`), from an `O4NormalForm` (so under `O4QuotientBound`).
* `FormalResearch.CohnElkies.MellinLiftIntegrals`: the two-edge integrals `I_main[F]`, `I_dual[D]` of a lift (`iMain`, `iDual`,
  `liftSymbol`), `K₀` on the imaginary axis (`mellinK0_imag_eq`) and their integrability for `HasU2` seeds.
* `FormalResearch.CohnElkies.AiryWindowInversion`: window smoothing `F_ψ` (`windowSmooth`), `W_X(w) = F̃_ψ(i c_s w)`, and the exact
  Airy inversion / reference identity (`HasU2.airy_inversion`, `airy_window_inversion`, `airy_reference_identity`).
* `FormalResearch.CohnElkies.FresnelBranch`: the branch-point term of `u1c:U3`(3) Piece C / `O.3(2)`: `∫ φ (iv)^{1/2} e^{iAv} dv =
  -√π φ(0) A^{-3/2} + O(A^{-2})` for `C²` amplitudes (`fresnel_branch`), by improper integration by parts and the Gaussian integral.
* `FormalResearch.CohnElkies.PieceCDecomposition`: exact decomposition `K₀ W = g e^{iψ} G_sm − γ₀ H_c (iv)^{1/2} χ₁ e^{iAv}` and the
  conditional assembly `pieceC_main_term` of `I_C = γ₀ A^{-3/2}/(2√π ξ) + O(ξ⁻¹A⁻²)` (smooth part and `C²` regularity of `χ₁H_c` as named hypotheses).
* `FormalResearch.CohnElkies.PieceCPhase`: the phase bounds `(u1c:psibd)` for `ψ = c Φ_Ph(εv; L)` (`pcPhase_psibd`: `ψ' ≥ A/2` on `|εv| ≤ τ_*`, `|ψ''| ≤ min(π²|v|/6, c^{2/3}/|v|)`, `|ψ'''| ≤ π²/3`).
* `FormalResearch.CohnElkies.PreEdgeCriterion`: unconditional concrete `GT.2b(1)–(3)` & `O.11y(3)`/`GT.4` tip offset
  for `twoScaleS`, unconditional `PE.3` reference & measure Mellin inversion (`pe3_reference_mellin_inversion`,
  `pe3_measure_inversion`), `pe3_remainder_integral_bound` (`O(c^{-2/3})`), `pe3_compact_origin_pos`, and
  Proposition `cepe:general` (`preEdge_general_pos`, with non-vacuity witnesses).
* `FormalResearch.CohnElkies.AirySymbolTransfer`: unconditional explicit global Morse coordinate (`airyMorseZ`,
  `airyMorseY`), Lemma `GT.1s` (`gt1s_scalar_airy_symbol_transfer`), and Lemma `GT.1` (`gt1_high_freq` and
  `gt1_low_freq`, with `airyTailSymbolSeed_nonvacuous`).

This umbrella is deliberately not imported by `FormalResearch.lean`.
-/
