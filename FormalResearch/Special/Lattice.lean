module

public import FormalResearch.Special.LatticeVarTail
public import FormalResearch.Special.LatticeOffset

/-!
# W1 phase-lattice summation (`lem:latticesum`, `lem:varcore`, `prop:offsetcore`)

Umbrella of the `Lattice*` modules (namespace `FormalResearch.Special.Lattice`), the lattice-summation
estimates of `Weyl/free_fermion/paper/parts/constants.tex`.  `LatticeVarTail` and `LatticeOffset` are the two top
modules; together they import all 26 `Lattice*` modules.

Setting: `ϰ = nc ≥ 1`, levels `S = {x ∈ [-X, X] : Θ(x) ∈ πℤ}` of a continuous strictly increasing `Θ` within `L^{-b}`
of `G(s) = θ₀ + s ℓ_Σ - ϰ arg Γ(½+is)`, `ℓ_Σ = ∑ log(L F_i)`, `L^{c_*/2} ≤ X ≤ L^{c_*}`.

**Proved** (standard axioms `propext, Classical.choice, Quot.sound`; the headline theorems carry `#guard_msgs` axiom guards).
* The phase: the Gauss-series branch `argGammaHalf` of `arg Γ(½+is)` is analytic on `|Im s| < ½`, odd, real on `ℝ`, with derivative
  `Re ψ(½+is)` on the real line (`LatticePhase`, `LatticePsi`, `LatticePhaseProps`); elementary bounds
  `Re ψ(½+ix) ≥ -3` and `Re ψ(x+iy) ≤ log(1+|y|) + 5` for `|Im| ≤ ¼` (`re_phaseDeriv_ge`, `re_phaseDeriv_le`); no Stirling,
  Fisher–Hartwig or Widom input.
* Abstract lattice analysis for an abstract calibrated phase `CalPhase`/`LevelData` (`LatticeSetup`–`LatticeII`): (o) level
  counts and spacing (`LevelData.card_levels_le`, `spacing_ge`, `spacing_le`), (i) (`latticeI_bound`) and (ii)
  (`latticeII_bound`).
* The Gamma phase is such a phase (`gamma_calPhase`, `LatticeGamma`–`LatticeSumGamma`), and `lem:latticesum` (o) and (ii) hold for it
  in paper form (`latticesum_gamma`, fixed-`L` form `latticesum_gamma_fixed`): error `≤ C C_φ L^{-b₁}` with `b₁ < b`,
  `b₁ < ϰ min(δ, ¼)`, `C, L₀` depending only on `nc, b, c_*, δ, κ, b₁, F_±`.
* `lem:varcore` (i) and (ii) for the Gamma phase (`varcore_gamma`, `varcore_tail_gamma`; `LatticeVar`, `LatticeVarTail`), using
  `∫ h G'/π = (ℓ_Σ + ϰ(1+γ))/(2π²)` (`integral_hvar_gdens`, from `lem:VI` in `Barnes`).
* `prop:offsetcore` (i) as a finite deduction from `lem:latticesum` (iii), taken as explicit hypotheses
  (`offsetcore_i_of_iii`).

**Not formalised.**
* `lem:latticesum` (iii) (the offset statement), and (i) for the Gamma phase as a concrete statement (only the abstract
  `latticeI_bound` is proved); no analytic obstruction is known, it needs the exact counting identities for `N_±`, Fubini for the finite
  sum, and the `t₀ ∈ ℤ` limit.
* `prop:offsetcore` (ii) (calibration), `lem:traceperturb` and `thm:tracecore` (Lidskii is available as `herm_lidskii_tnorm`
  in `MatrixAnalysis/Spectral`, but the trace perturbation is not formalised).
* The identification of `argGammaHalf` with the polar argument of `Γ(½+is)` (not needed by the lattice statements).
-/
