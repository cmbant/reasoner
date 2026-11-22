module

public import FormalResearch.ModularBootstrap.Constants
public import FormalResearch.ModularBootstrap.Crossing.Setup
public import FormalResearch.ModularBootstrap.Crossing.SumRule
public import FormalResearch.ModularBootstrap.Crossing.LemmaInputs
public import FormalResearch.ModularBootstrap.Crossing.BesselBridge
public import FormalResearch.ModularBootstrap.Crossing.GapFromPJ
public import FormalResearch.ModularBootstrap.Crossing.Bridge
public import FormalResearch.ModularBootstrap.Crossing.MehlerOddClosure
public import FormalResearch.ModularBootstrap.Crossing.MehlerOddMoment
public import FormalResearch.ModularBootstrap.Bessel.Defs
public import FormalResearch.ModularBootstrap.Bessel.IntegralRep
public import FormalResearch.ModularBootstrap.Bessel.VSeries
public import FormalResearch.ModularBootstrap.Bessel.LaplaceAux
public import FormalResearch.ModularBootstrap.Bessel.Laplace
public import FormalResearch.ModularBootstrap.Bessel.VAsymptotic
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries
public import FormalResearch.ModularBootstrap.Bessel.KernelComparison
public import FormalResearch.ModularBootstrap.Bessel.ComplexExpansion
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import FormalResearch.ModularBootstrap.SlitStrip.ConformalMap
public import FormalResearch.ModularBootstrap.SlitStrip.RealSlice
public import FormalResearch.ModularBootstrap.SlitStrip.Majorant
public import FormalResearch.ModularBootstrap.SlitStrip.PoissonJensenInput
public import FormalResearch.ModularBootstrap.SlitStrip.PoissonJensenNonvacuous
public import FormalResearch.ModularBootstrap.Rigidity.AiryRigidity
public import FormalResearch.ModularBootstrap.Blowup.TipMap
public import FormalResearch.ModularBootstrap.Blowup.PotentialAndWeight
public import FormalResearch.ModularBootstrap.Blowup.Majorant
public import FormalResearch.ModularBootstrap.Blowup.PropositionT
public import FormalResearch.ModularBootstrap.Integration.HankelBounds
public import FormalResearch.ModularBootstrap.Integration.StripKernel
public import FormalResearch.ModularBootstrap.Integration.StripTheoremA
public import FormalResearch.ModularBootstrap.Duality.CrossingMeasure
public import FormalResearch.ModularBootstrap.Duality.Farkas
public import FormalResearch.ModularBootstrap.Duality.DualMajorant
public import FormalResearch.ModularBootstrap.Duality.MomentProblem
public import FormalResearch.ModularBootstrap.Duality.MeasureCompactness
public import FormalResearch.ModularBootstrap.Duality.Coordinates
public import FormalResearch.ModularBootstrap.Duality.Compactness
public import FormalResearch.ModularBootstrap.Duality.LimitMeasure
public import FormalResearch.ModularBootstrap.Duality.StrongDuality
public import FormalResearch.ModularBootstrap.Duality.OptimalMeasure
public import FormalResearch.ModularBootstrap.ComplexBessel.BesselI0Sector
public import FormalResearch.ModularBootstrap.ComplexBessel.ComplexExpansion
public import FormalResearch.ModularBootstrap.ComplexBessel.StirlingOmega
public import FormalResearch.ModularBootstrap.ComplexBessel.LemmaS2
public import FormalResearch.ModularBootstrap.PoissonJensen.HankelInversion
public import FormalResearch.ModularBootstrap.PoissonJensen.HalfPlaneJensen
public import FormalResearch.ModularBootstrap.PoissonJensen.HarmonicMajorant
public import FormalResearch.ModularBootstrap.PoissonJensen.SlitMassAndDensity
public import FormalResearch.ModularBootstrap.PoissonJensen.LemmaPJAssembly

/-!
# Modular Bootstrap at Large Central Charge

Formalization of modular bootstrap Airy-scale lower bounds and spectral rigidity
(`CFT/modular_bootstrap/paper/`):

* `Constants`: Fold-tip constants (`xiStar`, `lambdaV`, `xiBar`, `betaTip`, `Aopt`, `LStar`) and
  normalized extremal profile `phiStar`.
* `Crossing.Setup`: Concrete fixed-weight crossing setup `(H_w)` (`virasoroProblem`,
  `n1SuperVirasoroProblem`), Bessel-series kernels `K_α`, Laplace identity, divided-difference
  positivity `V`, radial lift test class `\overline{\mathcal A}_w`, `M[g]`, `g_vac`, `T_weak`,
  `T_V`, `Δ_best`, and admissible crossing measures/spectra.
* `Crossing.SumRule`: `I_n` estimates and Cardy density sandwich, Mehler kernel regularisation,
  Lemma `FW-A` (isolating `MehlerOddMomentInput`), counting bound `fw:counting`, Lemma `FW-X`,
  and Theorem `FW-C` certification.
* `Crossing.LemmaInputs`: the uniform estimates `LemmaPJInput` (Lemma `PJ`, the one unproved analytic
  input of Theorem `A`) and `LemmaGapInput` (Lemma `G`, a consequence of `LemmaPJInput`).
* `Crossing.BesselBridge`: `kernelK 1 = besselK`, `virasoroProblem.cardyV = besselV`, and the transfer of
  Lemma B (a) and the pure-Bessel part of (d) to the concrete kernels.
* `Crossing.GapFromPJ`: Lemma `G` (`vlo:Gap`, `x₀ = 0.05`) derived from Lemma `PJ`:
  `LemmaPJInput → LemmaGapInput` (`lemmaGapInput_of_lemmaPJInput`).
* `Crossing.Bridge`: Virasoro bridge into `WeaklyFeasibleTest` (proving `hKa_ub` with
  `C_K = √(15/4)` and `hHalfMass`; `VirasoroStripInput` is the strip geometry plus `LemmaPJInput`, and the
  deep-lobe estimate is derived from it by `lemmaGapInput_of_lemmaPJInput`) and Theorem `A`
  for `T_weak`, `T_V`, and `Delta_best`.
* `Crossing.MehlerOddClosure`, `Crossing.MehlerOddMoment`: proof of `MehlerOddMomentInput` for every `w`
  (thermal differences are dense in the Fourier-odd radial `L²` functions; the Mehler kernel maps
  thermal differences to thermal differences and is `L²` in `y`), and the `_unconditional` forms of
  Lemma `FW-A`, Lemma `FW-X` and Theorem `FW-C`.
* `Bessel.*`: Lemma B (`vlo:Bessel`), pure-Bessel parts: `I₀, I₁, I₂` by power series
  (`Defs`), the integral representation (`IntegralRep`), `V = K_a - 2K_{a-1} + K_{a-2}` and
  part (a) (`VSeries`), Laplace asymptotics of `I₀` (`LaplaceAux`, `Laplace`), part (c) for real `x`
  and its consequences (`VAsymptotic`, `VCorollaries`), and the pure-Bessel part of (d)
  (`KernelComparison`); the complex-neighbourhood part of (c) is only a named hypothesis
  (`ComplexExpansion`).
* `SlitStrip.EntropyAndDeficit`: Slit-strip fold involution, edge mass Lemma `E`, sharp entropy
  Lemma `S`, `2.228 δ^{3/2}` deficit bound, Proposition `M`, and Theorem `A`.
* `SlitStrip.ConformalMap`: the conformal map `𝓑(z) = (2π)⁻¹ log((z-1)/(z(z+1)))` of the upper half-plane onto
  the slit strip (bijection, derivative, critical points `1 ± √2`, boundary behaviour, tip expansion),
  and its agreement with `slitBoundaryMap`, `slitInv`, `invJacobian`, `poissonKernel`.
* `SlitStrip.RealSlice`: the explicit preimage of `ξ_* - δ` and the proved `realSliceData : RealSliceData`.
* `SlitStrip.Majorant`: the harmonic majorant `U` on the real and imaginary axes, the closed form
  (G-deficit), the inverse-area identity and `U(i/2) = 0`.
* `SlitStrip.PoissonJensenInput`: `slitStripPoissonJensenInput` (geometry proved, `g_deficit` proved),
  `theorem_A_geometry`, and the single remaining geometric hypothesis `HarmonicMajorantIdentification`.
* `SlitStrip.PoissonJensenNonvacuous`: joint satisfiability of the remaining hypotheses.
* `Rigidity.AiryRigidity`: Local sign uncertainty/rigidity, Theorem `C`, and Theorem `R` `(R1)`–`(R3)`.
* `Blowup.TipMap`: Tip scaling map `bScale`, harmonic exponent `tipH`, tip distance `tipDist`,
  fold map `tipL`, slit map `slitBoundaryMapC`, disc oscillation/average bounds, and Lemma `T1`.
* `Blowup.PotentialAndWeight`: Complex potential blow-up (Lemma `T2`, `LemmaGPotentialInput`) and
  complex weight `W_C` asymptotic/upper bound via `BesselI0Asymptotic` (Lemma `T3`).
* `Blowup.Majorant`: Slit-strip bounds on real lines `Im ζ ≠ 0` (Lemma `T4`), minimal concrete
  test interface `BlowupTest`, tip-rescaled test `tipRescale`, and complex majorant (Lemma `T5`).
* `Blowup.PropositionT`: Uniform local envelopes, Montel exhaustion, left-tail control, **Proposition T**
  (i)–(vi) (`proposition_T`), construction of `BlowupFamilyPackage` / `RigidityFamilyPackage`
  discharging `propT_subseq`, and concrete test corollaries `blowup_theorem_C`,
  `blowup_theorem_R1`–`blowup_theorem_R3`.
* `Integration.HankelBounds`: Lemma B (b) (`∫|g| ≤ (4/π²) M[g]`, `sup|g| ≤ (8/π) M[g]`) and the integral
  bound of (d) (`∫|g| K_a ≤ 2e⁹² c'² M[g]`) for the concrete test class.
* `Integration.StripKernel`: Lemma B (d), second bound: `|G(b)| ≤ 4π e⁹² c'² M[g]` on `|Im b| ≤ 1/2` for the
  Hankel continuation `G` defined by its integral (agreement with `g(c'b²/3)` on the real axis is
  `PoissonJensen.hankelContinuation_ofReal`).
* `Integration.StripTheoremA`: Theorem `A` for `T_weak`, `T_V` and the optimal gap `Δ_best`
  (`theoremA_Delta_best`), unconditional: Lemma PJ for `realSliceData`, `majorantReal` is
  `stripPoissonJensen`.
* `Duality.CrossingMeasure`: crossing measures at a gap, Proposition `D1` (`proposition_D1`), and the
  measure-theoretic forms of the spectral Propositions 1, 2 (`proposition_P1`, `proposition_P2`).
* `Duality.DualMajorant`: Lemma `M` (`lemma_M`): the dual majorant `h = 2 ∫ Ξ_β ϑ(dβ)`, `w_*`, `C₀`
  (without the `ψ_k / w_*` clause).
* `Duality.Farkas`, `Duality.MomentProblem`, `Duality.MeasureCompactness`, `Duality.Coordinates`,
  `Duality.Compactness`, `Duality.LimitMeasure`: the proof of Theorem `E` (finite moment problems in the
  family `Ξ_β` by separation, weak compactness on the compactification `[T₀, ∞] ≅ [0, 1]`, transport).
* `Duality.StrongDuality`: Theorem `E` (`theorem_E`: crossing measures for `T < T_V`, the limit measure with
  `min supp = T_V`, and `T_V = max {τ : a crossing measure at gap τ exists}`).
* `Duality.OptimalMeasure`: Corollary `E1` as far as it follows without Theorem `C15`
  (`corollary_E1_exact_gap`, `corollary_E1_lower_bound`).
* `ComplexBessel.BesselI0Sector`: Complex `I₀` sector asymptotic (`besselI0C_sector_asymptotic`),
  bridge `integration_besselI0C_eq_blowup`, proof of `BesselI0Asymptotic` (`besselI0Asymptotic`), and
  unconditional Lemma `T3` corollaries (`lemma_T3_unconditional`, `lemma_T3_W_bound_unconditional`).
* `ComplexBessel.ComplexExpansion`: Complex Cardy expansion and Cauchy derivative bounds
  for `besselErrC`, proving `BesselComplexExpansion` (`besselComplexExpansion`).
* `ComplexBessel.StirlingOmega`: Stirling factorization (`vlo:stirling`) in `ω` (`gamma_mul_two_pi_t_cpow_neg`)
  with uniform `O(1/(c'|ω|))` remainder bound (`norm_stirlingS_sub_one_le`) and `ω`-derivative bound
  `O(1/(c'|ω|²))` (`norm_deriv_stirlingLogS_le`) down to `Re ω ≥ 0`.
* `ComplexBessel.LemmaS2`: Crude Legendre bound (`vlo:S2`, `lemma_S2`) via log-convexity/concavity of
  `s ↦ log V(e^s)` and the `x_c = ξ_*/2` derivative bound from `besselComplexExpansion`.
* `PoissonJensen.HankelInversion`: Hankel inversion `G(b) = g(c'b²/3)` on `ℝ` (`hankelContinuation_ofReal`),
  holomorphy of `G` on `|Im b| < 1/2` (`differentiableOn_hankelContinuation`), and closed-strip
  continuity (`continuousOn_hankelContinuation`).
* `PoissonJensen.HalfPlaneJensen`: upper half-plane Poisson--Jensen inequality for bounded holomorphic
  functions via Möbius transport to the unit disc (`halfPlane_poissonJensen`).
* `PoissonJensen.HarmonicMajorant`: proof of `HarmonicMajorantIdentification` (`h = U`, Lemma G
  `vlo:Gap`) via Phragmén--Lindelöf on the right half-plane.
* `PoissonJensen.SlitMassAndDensity`: `eSlitMass`, slit pullback change of variables
  (`setIntegral_slitPreimage_div_slitDensity`), entropy upper bound
  (`setIntegral_poisson_mul_log_slitDensity_le_entropy`), and a.e. nonvanishing of `G` on the slit
  preimage (`hankelContinuation_bdy_ne_zero_ae`).
* `PoissonJensen.LemmaPJAssembly`: full proof of `StripPoissonJensen` (Lemma `PJ`, `vlo:PJ`,
  `PoissonJensen.stripPoissonJensen`).
* `Integration.StripTheoremA`: unconditional **Theorem `A`** for `T_weak`, `T_V` and the optimal gap
  `Δ_best` (`theoremA_T_weak`, `theoremA_T_V`, `theoremA_Delta_best`), discharging
  `StripPoissonJensen` via `PoissonJensen.stripPoissonJensen`.
-/
