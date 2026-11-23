module

public import FormalResearch.SignUncertainty.ClarkTwoNode
public import FormalResearch.SignUncertainty.HermiteBiehlerUniq
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.SignUncertainty.HardyMellinIntertwiner
public import FormalResearch.SignUncertainty.HankelFiveHalvesWitness
public import FormalResearch.SignUncertainty.SignSeparation
public import FormalResearch.SignUncertainty.HankelBessel
public import FormalResearch.SignUncertainty.HankelBesselNat
public import FormalResearch.SignUncertainty.HankelBesselLaguerre
public import FormalResearch.SignUncertainty.RadialCompactnessKernel
public import FormalResearch.SignUncertainty.ShellLaplaceBase
public import FormalResearch.SignUncertainty.ShellGap
public import FormalResearch.SignUncertainty.ShellGapWitness
public import FormalResearch.SignUncertainty.ShellLaplaceZeros
public import FormalResearch.SignUncertainty.OddShellFamily
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
  `|𝓗_c f| ≤ M[f]`, `HankelKernelData` from `HankelAntiderivFacts`, agreement with the natural-order
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
* `FormalResearch.CohnElkies`: Stieltjes/cardinal resolvent, Mellin–Airy, lobe saddle,
  finite-dimensional Gaussian, and Fourier interpolation lemmas.
-/
