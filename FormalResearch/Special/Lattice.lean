module

public import FormalResearch.Special.LatticeVarTail
public import FormalResearch.Special.LatticeOffset
public import FormalResearch.Special.LatticeOffsetGamma
public import FormalResearch.Special.TraceFunctional
public import FormalResearch.Special.TraceCoreMain

/-!
# W1 phase-lattice summation (`lem:latticesum`, `lem:varcore`, `prop:offsetcore`, `lem:traceperturb`, `thm:tracecore`)

Umbrella of the `Lattice*` modules (namespace `FormalResearch.Special.Lattice`) and the `Trace*` modules (namespace
`FormalResearch.Special.TraceCore`), the lattice-summation and trace estimates of
`Weyl/free_fermion/paper/parts/constants.tex`.  `LatticeVarTail`, `LatticeOffset`, `LatticeOffsetGamma`, `TraceFunctional` and
`TraceCoreMain` are the top modules; together they import all 31 `Lattice*` modules and all 6 `Trace*` modules.

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
* `lem:latticesum` (iii) for the Gamma phase in paper form (`latticesum_gamma_iii`; `LatticeNu`, `LatticeIII`, `LatticeIIIGamma`):
  `S_ν = ∑_{x∈S}[ν(2πx) - 1_{x<0}]` is within `C L^{-b₁}` of `{t₀} - ½` (for `{t₀} ≠ 0`) and of `t₀ - ½ + ℤ`, `t₀ = Θ(0)/π`, with
  `b₁ < b`, `b₁ < ϰ/4` (the weight `w = π/(2cosh²πs)` is analytic in `|Im s| ≤ ¼`, so `δ` plays no role); the case `t₀ ∈ ℤ` is
  proved directly from the exact identity `LevelData.offset_identity`; abstractly `latticeIII_bound`.
* `prop:offsetcore` (i) and (ii) for the Gamma phase, unconditionally (`offsetcore_gamma`, `LatticeOffsetGamma`; the finite
  deduction `offsetcore_i_of_iii` of `LatticeOffset` is its input), with `ε_𝔱 = L^{-b₁} + ϰ X log L ε_λ + ε_μ`.
* `lem:traceperturb` (`traceperturb`, `traceFn_sub_le_lipschitz`; `TraceFunctional`): `|∑ f(λ_j(A)) - ∑ f(λ_j(B))| ≤ sup|f'| ‖A-B‖₁`
  for Hermitian `A, B`, via Lidskii (`herm_lidskii_tnorm`).
* `thm:tracecore` for the Gamma phase (`tracecore_gamma`, `tracecore_gamma_opnorm`; `TraceCoreMain`; matrix part
  `tracecore_decomp`, `TraceBlock`, `TraceCoreDecomp`; weights `Admissible`, `TraceAdmissible`; power bookkeeping `TraceCoreAsymp`;
  tail sums `sum_exp_rate_le`, `LatticeTailC`): for `(σ,δ,κ)`-admissible `h`, (TC) and (FM_σ) as hypotheses,
  `‖Tr h(C) - ∫ h(ν(2πs)) g(s) ds‖ ≤ K L^{-min(σa/3, b₁)}`, `g = (ℓ_Σ - ϰ Re ψ(½+is))/π`.  Non-sharp constants; the piecewise
  linear cutoff replaces the paper's smooth one.

**Not formalised.**
* (i) of `lem:latticesum` for the Gamma phase as a standalone statement (only the abstract `latticeI_bound`, used inside (ii),
  (iii) and `thm:tracecore`).
* The identification of `argGammaHalf` with the polar argument of `Γ(½+is)` (not needed by any statement here).
* The verification of the hypotheses (TC) and (FM_σ) of `thm:tracecore`, and of the lattice data, in the cases (G) and (H) of the
  paper (the instances and the Hermite asymptotics: for the Hermite functions only the Airy-edge shape `hermite_airy_edge` of `HermiteAiry` is formalised, with the
  amplitude `κ` known only up to order (`hermite_kappa_order` of `HermiteKappa`), not the bulk phase or the lattice data); and everything downstream of `thm:tracecore` (`res:constants`, `intoffset`).
-/
