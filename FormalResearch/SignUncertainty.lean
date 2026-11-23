module

public import FormalResearch.SignUncertainty.ClarkTwoNode
public import FormalResearch.SignUncertainty.HermiteBiehlerUniq
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.SignUncertainty.HardyMellinIntertwiner
public import FormalResearch.SignUncertainty.HankelFiveHalvesWitness
public import FormalResearch.SignUncertainty.SignSeparation
public import FormalResearch.SignUncertainty.HankelBessel
public import FormalResearch.SignUncertainty.HankelBesselMoments
public import FormalResearch.SignUncertainty.HankelBesselMellin
public import FormalResearch.SignUncertainty.HankelAntiderivCalculus
public import FormalResearch.SignUncertainty.HankelAntiderivLimit
public import FormalResearch.SignUncertainty.HankelAntiderivValue
public import FormalResearch.SignUncertainty.HankelBesselData
public import FormalResearch.SignUncertainty.HankelBesselNat
public import FormalResearch.SignUncertainty.HankelBesselLaguerre
public import FormalResearch.SignUncertainty.RadialCompactnessKernel
public import FormalResearch.SignUncertainty.ShellLaplaceBase
public import FormalResearch.SignUncertainty.ShellGap
public import FormalResearch.SignUncertainty.ShellGapWitness
public import FormalResearch.SignUncertainty.ShellLaplaceZeros
public import FormalResearch.SignUncertainty.OddShellFamily
public import FormalResearch.SignUncertainty.ElementaryIdentities
public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.HankelMellinKernel
public import FormalResearch.SignUncertainty.MellinStrip
public import FormalResearch.SignUncertainty.MellinStripAnalytic
public import FormalResearch.SignUncertainty.MellinMajorantH
public import FormalResearch.SignUncertainty.MellinMajorantHId
public import FormalResearch.SignUncertainty.MellinGrowth
public import FormalResearch.SignUncertainty.MellinHGrowth
public import FormalResearch.SignUncertainty.MellinMajorant
public import FormalResearch.SignUncertainty.MellinMajorantBound
public import FormalResearch.SignUncertainty.MellinDecay
public import FormalResearch.SignUncertainty.MellinInversion
public import FormalResearch.SignUncertainty.DeepLobeKernel
public import FormalResearch.SignUncertainty.DeepLobeIntegral
public import FormalResearch.SignUncertainty.DeepLobePointwise
public import FormalResearch.SignUncertainty.DeepLobeNumerics
public import FormalResearch.SignUncertainty.DeepLobeRegionII
public import FormalResearch.SignUncertainty.DeepLobeRegionI
public import FormalResearch.SignUncertainty.DeepLobeMass
public import FormalResearch.SignUncertainty.MontelHol
public import FormalResearch.SignUncertainty.StripGExpansion
public import FormalResearch.SignUncertainty.RadialKernelLimit
public import FormalResearch.SignUncertainty.RadialXiRepr
public import FormalResearch.SignUncertainty.RadialXiMain
public import FormalResearch.SignUncertainty.ParamIntegral
public import FormalResearch.SignUncertainty.RadialDomination
public import FormalResearch.SignUncertainty.RadialIntegrand
public import FormalResearch.SignUncertainty.RadialValueLimit
public import FormalResearch.SignUncertainty.RadialValueMain
public import FormalResearch.SignUncertainty.RadialDerivative
public import FormalResearch.SignUncertainty.RadialDerivMain
public import FormalResearch.SignUncertainty.RadialDerivLimit
public import FormalResearch.SignUncertainty.RadialLimitW
public import FormalResearch.SignUncertainty.RadialLimitXi
public import FormalResearch.SignUncertainty.RadialContour
public import FormalResearch.SignUncertainty.RadialXiEntire
public import FormalResearch.SignUncertainty.RadialShift
public import FormalResearch.SignUncertainty.RadialAiryReal
public import FormalResearch.SignUncertainty.RadialAiryBound
public import FormalResearch.SignUncertainty.RadialProfileValue
public import FormalResearch.SignUncertainty.RadialProfileDeriv
public import FormalResearch.SignUncertainty.RadialProfileFatou
public import FormalResearch.SignUncertainty.RadialCompactness
public import FormalResearch.SignUncertainty.RadialCompactnessProof
public import FormalResearch.SignUncertainty.Headlines
public import FormalResearch.CohnElkies

/-!
# Sign Uncertainty and Cohn–Elkies Bootstrap

Umbrella collecting sign-uncertainty theorems and Cohn–Elkies analytic lemmas:

* `FormalResearch.SignUncertainty.ClarkTwoNode`: Clark two-node sign uncertainty and equality
  characterization (`CFT/common/clark_airy.tex`, Theorem 1.2).
* `FormalResearch.SignUncertainty.HermiteBiehlerUniq`: polynomial Hermite–Biehler uniqueness
  and `m = 2` `L^1` norm identity (`CFT/common/clark_airy.tex`, Lemma `H.2a` and `(eq:hb-two-node-norm)`).
* `FormalResearch.SignUncertainty.RadialRigidity`: all-level Hermite–Biehler Airy-scale lower
  bound and profile/origin rigidity (`CFT/sign_uncertainty/paper/general_theorems.tex`, Theorem 7.5).
* `FormalResearch.SignUncertainty.HardyMellinIntertwiner`: Hardy–Mellin intertwiner
  `(ℐ_c f)(Δ)` and `T_c^{+1} ≤ T_c^{-1}`, `A_+(d) ≤ A_-(d)` (`general_theorems.tex`, Prop 7.9a).
* `FormalResearch.SignUncertainty.HankelFiveHalvesWitness`: explicit `c = 5/2` (`d = 5`) Bessel
  `J_{3/2}` non-vacuity witness for Proposition 7.9a.
* `FormalResearch.SignUncertainty.SignSeparation`: odd Laguerre origin constraint (`Prop 7.9b`)
  and sign separation of bounded remainders (`Thm 7.9c`, `general_theorems.tex`).
* `FormalResearch.SignUncertainty.HankelBessel`, `HankelBesselNat`, `HankelBesselLaguerre`: the concrete
  real-order Bessel Hankel kernel `K^{(c)}` of `fourier_mellin.tex` (`|K| ≤ 1`, the transform `𝓗_c` and
  `|𝓗_c f| ≤ M[f]`, unconditional `HankelKernelData` (`∫_0^R J_{c-1} → 1` proved by integration by parts, a Lyapunov decay bound and the `+1` Laguerre mode), agreement with the natural-order
  Bessel function) and the Laguerre modes `𝓗_c e^{-2πΔ} = e^{-2πΔ}`, `𝓗_c u₀ = -u₀`
  (`general_theorems.tex`, Prop 7.9b input).
* `FormalResearch.SignUncertainty.RadialCompactnessKernel`: the `s`-derivative identity
  `∂_s(ξ_c^{-1} K_c(w,s)) = ξ_c^{-1}(w - ε_c²) ξ_c^{-1} K_c(w,s)` of the Mellin kernel (kernel level of the `C¹`
  clause of `lem:radial-compactness`; the compactness argument itself is not formalised).
* `FormalResearch.SignUncertainty.ShellLaplaceBase`: Airy–Laplace transform, `ShellHBData`,
  even-`m` Laplace sign, factored ODE, and one-profile LP reduction (`ce_shells.tex`, Prop `H.14'`).
* `FormalResearch.SignUncertainty.ShellGap`: conditional Mellin origin-floor (`shell_reduction_lower`)
  and packaged subsequential core of Theorem `H.14` (`theorem_H14_subseq_bounds`, `theorem_H14_strict_gap`).
* `FormalResearch.SignUncertainty.ShellGapWitness`: explicit `ShellHBData.airy` (`m = 1`)
  consistency witnesses for `ShellGapPackage` and `ShellReductionPackage`.
* `FormalResearch.SignUncertainty.ShellLaplaceZeros`: positive zero multiplicity `≤ m - 1`,
  near-`0⁺` and large-`y` positivity, and `m = 3` trichotomy (`ce_shells.tex`, Corollary `H.14b`).
* `FormalResearch.SignUncertainty.OddShellFamily`: analytic odd-level Hermite–Biehler shell gap
  configurations (`ce_shells.tex`, Corollary `H.14a` / `thm:ce-odd-family`) for every odd `m ≥ 3`.
* `FormalResearch.SignUncertainty.ElementaryIdentities`: the O.4(2) contraction algebra (`u1co:O4`),
  and the Laplace-type integral of Lemma U.1(1) (`u1c:U1`).
* `FormalResearch.SignUncertainty.Radii`: concrete Euclidean radii `A_sign^±(d)`, the prescribed-shell
  Cohn–Elkies class and `u_LP`, the Bessel-kernel Hankel thresholds, and the bridge to the abstract
  `HankelKernelData` development (`sign_uncertainty_core.tex`, introduction).
* `FormalResearch.SignUncertainty.HankelMellinKernel`: the Mellin transform `Φ_c(z)` of the Hankel kernel, the
  Mellin–Fubini identity for `𝓗_c` and Weber's integral in product form (from the Laguerre eigenfunction),
  the first step of `gt:7.4(1)` (`fourier_mellin_proofs.tex`).
* `FormalResearch.SignUncertainty.MellinStrip`, `MellinStripAnalytic`: `gt:7.4(1)` for `f ∈ 𝒜_c^ε`, `c > 3/2`: the
  Mellin strip `M̃_f` (`mellinStrip`), integrability, reflection `M̃_f(c-z) = ε M̃_f(z)` on `0 < Re z < c`
  (`mellinStrip_reflection`), continuity on `0 < Re z ≤ c`, holomorphy on `0 < Re z < c` and the edge
  bound `|M̃_f(c+iy)| ≤ Γ(c) M[f]/|Γ(c+iy)|` (`norm_mellinStrip_edge_le`).
* `FormalResearch.SignUncertainty.MellinMajorantH`, `MellinMajorantHId`: the majorant exponent `ℋ̂` (`hInt`) on the closed strip
  `-1 < Re z < 2` from `Γ`-ratio logarithms, with `ℋ̂(1 - z) = ℋ̂(z)`, `ℋ̂(0) = ℋ̂(1) = 0`
  (`hInt_one_sub`), identified with `stripH` on `0 ≤ Re z < 1` (`hInt_eq_stripH`); the input to the
  Phragmén–Lindelöf majorant of `gt:7.4(2)`.
* `FormalResearch.SignUncertainty.MellinGrowth`, `MellinHGrowth`, `MellinMajorant`, `MellinMajorantBound`:
  `gt:7.4(2)` for `c > 3/2`, `ε = ±1`, `f ∈ 𝒜_c^ε`: crude growth bounds, the glued function `W = Fm e^{-cℋ̂}(1+ζ)^{-1/2}`,
  the edge bounds `|W| ≤ M[f] e^{1/(6c)}` and Phragmén–Lindelöf, giving
  `|M̃_f(c(1-ζ))| ≤ M[f] |1+ζ|^{1/2} exp(c Re ℋ(ζ) + 1/(6c))` on `0 ≤ Re ζ < 1`
  (`norm_mellinStrip_le_majorant`, and `..._stripH` with `ℋ = stripH`).
* `FormalResearch.SignUncertainty.MellinDecay`, `MellinInversion`: Step 1 of `lem:radial-compactness`: left-edge decay
  `|mellinRaw f (x₁+iy)| ≲ (1+|y|)^{-(c-2x₁)}` (reflection + Stirling), three-lines (Mathlib Hadamard) power decay on
  `x₁ ≤ Re z ≤ c`, integrability on `Re z = σ`, `σ+1 < c`, and Mellin inversion `mellin_inversion_f`
  `f(Δ) = (1/2π) ∫ Δ^{-(σ+iy)} mellinRaw f (σ+iy) dy`.
* `FormalResearch.SignUncertainty.DeepLobeKernel`, `DeepLobeIntegral`, `DeepLobePointwise`, `DeepLobeNumerics`,
  `DeepLobeRegionII`, `DeepLobeRegionI`, `DeepLobeMass`: Step 2 of `lem:radial-compactness`: the vertical decay of the
  exact Mellin kernel `‖K₀(s+iτ,ξ)‖`, the lobe integral, the pointwise bound `ρ₀|f|(cξ)` (`rho0_abs_f_le`), and the
  deep-lobe mass bound `deep_lobe_mass_thm` (`c ≥ 56`, `R ≥ 1`: `≤ 8 M[f] (e^{-5R^{3/2}} + e^{-c/25})`).
* `FormalResearch.SignUncertainty.MontelHol`, `StripGExpansion`, `RadialKernelLimit`, `RadialXiRepr`, `RadialXiMain`,
  `ParamIntegral`, `RadialDomination`, `RadialIntegrand`, `RadialValueLimit`, `RadialValueMain`, `RadialDerivative`,
  `RadialDerivMain`, `RadialDerivLimit`: Steps 3 of `lem:radial-compactness`: Montel's theorem on `{Re w > 0}`
  (`montel_rightHalfPlane`), `‖S̃₀(ζ) - π² ζ³/36‖ ≤ 10‖ζ‖⁵`, the rescaled kernel and its limit
  (`radialK_tendsto`, `radialK_norm_le`), the representation `Ξ_c(s) = ∫ radialA` (`radial_xi_repr`), and the locally
  uniform limits `radial_value_limit`, `radial_deriv_limit` of `Ξ_c`, `Ξ_c'` along a sequence with
  `W_{c_k} → W`.
* `FormalResearch.SignUncertainty.RadialLimitW`, `RadialLimitXi`, `RadialContour`, `RadialXiEntire`, `RadialShift`,
  `RadialAiryReal`, `RadialAiryBound`, `RadialProfileValue`, `RadialProfileDeriv`, `RadialProfileFatou`,
  `RadialCompactnessProof`: Step 4 of `lem:radial-compactness`: the Montel limit `W` (`exists_radialW_limit`), the
  entire limit `Ξ_W` (`differentiable_XiL`), contour independence (`limInt_integral_shift`), the Airy-class bound
  `‖F(z)‖ ≤ C (1+|z|)^{1/2} e(z)` (`radialF_airy_bound`), the identification of the window profiles with `Re Ξ_c` and
  the locally uniform convergence of profiles and derivatives, Fatou for the `L¹` clause, and the assembly
  `profile_compactness_thm`, `radial_compactness`.
* `FormalResearch.SignUncertainty.RadialCompactness`: the statement of `lem:radial-compactness` (`RadialCompactness`:
  window-profile compactness with the `C¹` clause; proved as `radial_compactness`; the deep-lobe mass bound is
  `deep_lobe_mass_thm`) and the lower half of `gt:7.5` at one level derived from it
  (`radial_rigidity_lower_of_compactness`).
* `FormalResearch.SignUncertainty.Headlines`: the headline theorems `thm_intro_radii`,
  `thm_intro_separation`, `thm_intro_gap_i/ii/iii` of Paper I, each proved from one input structure
  whose fields are the open TeX theorems (milestone M0 skeleton; see `PLAN.md` §5).
* `FormalResearch.CohnElkies`: Stieltjes/cardinal resolvent, Mellin–Airy, lobe saddle,
  finite-dimensional Gaussian, and Fourier interpolation lemmas.
-/
