# Paper J, conditional pipeline: plan, dependency DAG, Layer-4 list

Status: **statement freeze** (this commit group): definitions and Prop-valued statements only, no proofs, no placeholder proofs, no added axioms.
Paper: `Weyl/jacobi_eigenvectors/paper/parts/*.tex` on `origin/agents/m7-m1-global-racah` of QIprojects.
Layers: **L1** engine completion (`thm:eng-corr`, per-patch stability); **L2** Theorem A from engine + `ChartInputs`; **L3** Theorem B from L2 + chart inputs;
**L4** discharge the chart / special-function hypotheses (NOT this phase).  Namespace `FormalResearch.JacobiEigenvectors.<Sub>`.

Relocation notes (main session): the engine `FormalResearch/JE/` will move to `FormalResearch/JacobiEigenvectors/Engine/` (imports here are `FormalResearch.JE.*` until then);
`FormalResearch/JB/` (Theorem B reduction, `OneStepInputs`, `jb_onestep`, `thm_B_conditional`) stays and is to be folded into `TheoremB/` later.
`FormalResearch/JacobiEigenvectors.lean` is an umbrella stub, **not** in `FormalResearch.lean` yet.

## Files of the freeze (all build; `lake build FormalResearch.JacobiEigenvectors`)

| file | content |
|---|---|
| `Setting/JacobiFamily.lean` | `SymbolFamily`, `jacobiMat`, `IsEigenSystem`, `JacSol`, `DM`, `EK`, `Hyp` (H1-H3), `frozenFamily`, `mirrorFamily`, `negFamily` (+ proved identities) |
| `Charts/LadderChain.lean` | `LadderData`, `.Valid` (engine hypotheses, eq:eng-UC1), `.Concl`, `.Stability` (statement of thm:eng-volterra for per-patch ladders) |
| `Charts/ParabolicCylinder.lean` | `k2, Mbal, Ewell, Ebar, kappaBal, Molv`; `ParabolicCylinderFacts` (DLMF 12.2/12.8, Olver envelopes, connection) |
| `Charts/Regularity.lean` | `BoundedC2`, `JetRegJ` (plain regularity bounds replacing lem:smo-budget) |
| `Charts/BulkWeber.lean` | `BulkWeberChart` (hard-edge Weber chart, per energy block), `BulkPhaseInputs` (lem:smo-bulkphase (4)) |
| `Charts/SoftParabolicCylinder.lean` | `SoftEdgeChart` (two-patch chain Weber + PC), `pcMinus`, `aPC`, `lamL`, `psiHatL` |
| `Charts/TransferCoefficients.lean` | `TransferInputs` (I2 coefficients, parity eq:thb-parity) |
| `Charts/ChartInputs.lean` | `ChartInputs` bundle (frozen family, bulk blocks, four soft charts, mirror/cover relations) |
| `TheoremA/Comparison.lean`, `Statements.lean` | glue vectors, `psiHatVec`, `envVec`; statements of A(i), A(ii), prop:tha-W/W2, lem:tha-win/M/count, prop:l2jets, thm:smo-spec, lem:hyp-morse |
| `TheoremA/GeometryStatements.lean` | lem:tha-geom (a)-(d) per block (`TheGeometry`) |
| `TheoremA/EigenvalueStatements.lean` | Step 0 (`StepZero`, `StepZeroD0`, `SpectrumCovered`), cor:eigen (a)-(d) (`CorEigen`) |
| `TheoremB/ComparisonMatrix.lean`, `Statements.lean` | `compMatrix`; prop:tha-splice, lem:tha-Mflat, lem:tha-collar, `ChartPair`, `TransferBundle`, prop:thb-inputs, thm:B, cor:thb-Dm |

## Dependency DAG of proof obligations (hyp = hypotheses used besides the setting; size in lines; diff: E easy, M medium, H hard, VH VERY HARD)

Legend of hypotheses: LS = `LadderData.Stability`, BW/SE = bulk/soft chart, PC = `ParabolicCylinderFacts`, BP = `BulkPhaseInputs`, TB = `TransferBundle`.

### Layer 1 (engine, `Engine/`, after the move)
| id | Lean name to prove | paper | hyp | size | diff |
|---|---|---|---|---|---|
| L1.1 | `LadderData.Stability` | thm:eng-volterra (a)+(b), per-patch ladders | `JE.ladder_S1/S2/residual_*`, `volterra_multi` | 150 | E (copy `ladder_pair_stability`, patchwise) |
| L1.2 | defect bound `LadderData.Valid.defect0/1`, `cas_lb` from a corrector construction | thm:eng-corr, lem:eng-transport, prop:eng-corr1 | JE.Kernel/Defect | 600 | H (corrector recursion, derivative bookkeeping) |
| L1.3 | `exists_eigenSystem`, `eigVec_JacSol` (columns solve `JacSol`), `bondA_pos` | setting | spectral theorem | 200 | E |
| L1.4 | `casD_const`, `casD' = sum p q` (Green) | lem:eng-abel (used by lem:tha-count) | JE.Casoratian | 120 | E |

### Layer 2 (Theorem A), file / agent
| id | Lean name | paper | hyp | size | diff |
|---|---|---|---|---|---|
| L2.G1 | `HypMorseEquiv` | lem:hyp-morse | none | 250 | M (1-d real analysis) |
| L2.G2 | `HypOpen` | lem:hyp-morse (openness) | G1 | 150 | M |
| L2.G3 | `FrozenStandard` | sec:tha-standing | G2 | 200 | M |
| L2.G4 | lem:tha-geom (a)-(d) (**statement frozen**: `TheoremA/GeometryStatements.lean` (`TheGeometry`: `GeomBulk`, `GeomCollision`, `GeomMargins`, `GeomSoft`, `GeomSoftLower`); feeds `overlap_in_well`, `uc_spec`; per-block and per-neighbourhood, F-geom, F-geom2) | lem:tha-geom | G1 | 300 | M |
| L2.C1 | `BulkSolutionBound` (= `thm:cha-I`, `cor:cha-I-general`) | thm:cha-I | BW.valid, L1.1 | 120 | E-M (JacSol to `Lh`; `volTheta` smallness for `h<=h1`) |
| L2.C2 | `PropThaW` (2) normalisation, `hat N ~ h^{-1/4}`, collars | prop:tha-W | C1, BW (`M_osc`, `W_osc`, `collar_lb`) | 400 | M |
| L2.C3 | `PropThaWin` | lem:tha-win | PC, SE.zeta_deriv | 400 | M (many routine inequalities) |
| L2.C4 | `PropThaM` | lem:tha-M | C3, PC (virial identity, continuity in `a`) | 350 | H (compactness in `a`; `Gamma` continuity; two-site Casoratian) |
| L2.C5 | `PropThaCount` | lem:tha-count | L1.4 | 200 | M |
| L2.C6 | `PropThaW2` (1): through the soft edge, rescaling `lambda`, `|lambda_L| ~ lambda kappa_bal` | prop:tha-W2 (1), thm:cha-PC | L1.1 for two patches, SE.valid, PC | 600 | VH (forbidden-overlap rescaling, S3) |
| L2.C7 | `PropThaW2` (2)-(4): eigenvectors, quantisation (label = index), one shift short | prop:tha-W2 | C3, C4, C5, C6, PC connection `M_-(a)` | 900 | VH |
| L2.C8 | Step 0: eigenvalues in `[X_s^- - Ch^2, X_s^+ + Ch^2]` (**statement frozen**: `StepZero`, `StepZeroD0`, `SpectrumCovered` in `TheoremA/EigenvalueStatements.lean`; F-E1) | app_thmA Step 0 | L2.S4 | 300 | H |
| L2.C9 | `ThmAii` | thm:A(ii) | C2, C7, C8, F-A3 | 150 | E-M |
| L2.S1 | bulk windows: lem:smo-bulkphase (1)-(3) | lem:smo-bulkphase | C2, C5, PC.phase_osc | 400 | M-H |
| L2.S2 | phase of the comparison Casoratian to eigenvalue-level phase (from `BP.casoratian` and `BulkSolutionBound`) | lem:smo-bulkphase (4) | BP | 250 | M |
| L2.S3 | Taylor substitution `t=h` of `Sigma_j(X,t)` (`C^{2M+1}` in `(X,t)`) | thm:smo-spec, "substitution" | BP.Sigma_reg | 250 | M |
| L2.S4 | lem:smo-SM: `||J - tilde J|| <= C h^{M+1}`, eigenvalues shift (Weyl) | lem:smo-SM | none | 200 | E-M |
| L2.S5 | matching on overlaps and density (`S_l^I = S_l^{I'}`) | thm:smo-spec, "Matching" | S1-S3, C7 | 500 | H |
| L2.S6 | `ThmSmoSpec` (existence, uniqueness, extension independence) and `ThmAi` | thm:smo-spec, thm:A(i) | S1-S5, C7 | 400 | VH (assembly across `K`, cover, soft windows) |
| L2.S7 | `S_j` depends only on jets `<= j`; `C^infty` jets | thm:smo-spec | S6 | 250 | M |
| L2.E | cor:eigen (a)-(d): `S_1` formula, inverse quantisation, gap `>= c h`, counting (**statements frozen**: `CorEigenS1`, `CorEigenInverse`, `CorEigenGap1`, `CorEigenGapM`, `CorEigenCount`, `CorEigen` in `TheoremA/EigenvalueStatements.lean`; F-E2..E4) | cor:eigen | S6 | 700 | H |
| L2.J | `PropL2Jets` | prop:l2jets | C9 (truncated family), L2.S4, L2.E (gap) | 350 | M-H (eigenvector perturbation along `J_s`) |

### Layer 3 (Theorem B)
| id | Lean name | paper | hyp | size | diff |
|---|---|---|---|---|---|
| L3.1 | `PropThaSpliceBulk`, `PropThaSpliceSoft` | prop:tha-splice (a), (b) | C2, C7 | 300 | M |
| L3.2 | `PropThaSpliceTwoOrders` | prop:tha-splice (c) | L3.1, C2, C7, Cauchy-Schwarz | 150 | E-M |
| L3.3 | `PropThaMflat` | lem:tha-Mflat | C4 (cut `s = Z_{n_c}`), SE | 300 | M |
| L3.4 | `PropThaCollar` | lem:tha-collar (1) | C6, C7 (discrete maximum principle, forbidden margin) | 400 | H |
| L3.5a | bulk charts to `JB.Chart` + `Chart.Ok` (transfer = row of `shift_up`; Schur via `jb_schur_of_C2/inv/div`; closure of `FullC2` under products and quotients) | app_thmB (I2)-(I4) bulk | TB, C2, L3.1 | 500 | M-H |
| L3.5b | soft halves to `JB.Chart` | app_thmB (I2)-(I4), (I5) soft | TB, L3.3, L3.4 | 500 | H |
| L3.5c | assembly `PropThbInputs`: blocks (finite by compactness), hosts at extreme splices, `outside`, `G1_col`, `U_orth`, `eps5` form | prop:thb-inputs | L3.2, L3.5a/b | 400 | H |
| L3.D | cor:thb-stable (Fourier--Schur perturbation lemma, Bhatia--Davis--McIntosh): gaps `>= c h` and `||J' - J|| <= K h^{m+1}` give `||U' Delta - U|| <= C_* K h^m` (**not in the DAG before; statement not frozen**; needed for `CorThbDm`) | cor:thb-stable | L2.E (gap) | 250 | M |
| L3.Dm | `CorThbDm` (**statement frozen**: `TheoremB/Statements.lean`) | cor:thb-Dm | L2.J, L3.5c for `truncFamily F m`, L3.D | 150 | E-M |
| L3.B | `ThmB` from `jb_onestep` with constants uniform in `mu` (copy of `thm_B_conditional` proof; F-B2) | thm:B | L3.5c | 150 | E |

## Assignment (disjoint files; independent agents)

* **Agent 1** `Engine/LadderStability.lean` (L1.1), then `Engine/Corrector.lean` (L1.2).  **Agent 2** `Setting/EigenSystem.lean` (L1.3), `Engine/Green.lean` (L1.4), `TheoremA/Count.lean` (L2.C5).
* **Agent 3** `TheoremA/Geometry.lean` (L2.G1-G4).  **Agent 4** `TheoremA/WindowEnvelopes.lean` (L2.C3, L2.C4).  **Agent 5** `TheoremA/BulkProof.lean` (L2.C1, L2.C2, L2.S1).
* **Agent 6** `TheoremA/SmoothSpectrum.lean` (L2.S2-S4, L2.S7), `TheoremA/L2Jets.lean` (L2.J) after L2.E.  These are independent of the soft-edge work.
* **First pass by a stronger model** (VERY HARD, then handed to routine agents for bookkeeping): L2.C6 and L2.C7 (`TheoremA/SoftProof.lean`: the rescaling choice that makes (S3) hold, the Casoratian sign analysis for the quantisation), L2.S6 (assembly of the eigenvalue rule; decides the cover and which statements `S5` needs).  Also a stronger-model review of the statements L2.E, L3.4, L3.5c before work starts.
* Layer 3 after L2: **Agent 7** `TheoremB/Splice.lean` (L3.1, L3.2), `TheoremB/Mflat.lean` (L3.3); **Agent 8** `TheoremB/Collar.lean` (L3.4); **Agent 9** `TheoremB/InputsBulk.lean`, `TheoremB/InputsSoft.lean` (L3.5a/b); `TheoremB/Assembly.lean`, `TheoremB/ThmB.lean` (L3.5c, L3.B) by the reviewer.
* Critical path: L1.2 and L1.1 -> L2.C1 -> L2.C6 -> L2.C7 -> L2.S6 -> L2.E -> L2.J; and L2.C7 -> L3.4 -> L3.5b -> L3.5c -> L3.B.

## The Layer-4 list (residual hypotheses of the whole pipeline) and the exact paper statement behind each

1. `ParabolicCylinderFacts` (DLMF 12.2.2, 12.2.4, 12.2.10, 12.8.2-3, 12.8.6-7, 12.2.15-16; Olver Ch.11 Thm 3.1, Ch.6 Thm 2.2): lem:cha-PCenv (1b), (2), (3); eq:tha-conn (`M_-(a)`);
   `ode`, `wronsk`, `shift_*` (lem:cha-weber-ladder (2)); `phase_osc` (DLMF 12.10.18, lem:smo-bulkphase (1)).  Needs a definition of `U, V` (none in Mathlib).
2. `BulkWeberChart`: coordinate `Y`: prop:cha-halfrow (a), lem:cha-weber-coord (1)-(2), eq:tha-matchF/O; ladder (SM1)-(SM3) and annihilation: lem:cha-weber-ladder (1), (3), eq:cha-annih;
   envelopes and weights: lem:cha-weber-env (1)-(3), lem:cha-W0; `W_osc`, `M_osc`, `seed_pos`, `collar_lb`, `theta_le`; defect/Casoratian bounds `defect*`, `cas_lb`, `A_bd`, `B_bd`: thm:eng-corr + lem:cha-weber-coord (3) (this is L1.2, not Layer 4 proper).
3. `SoftEdgeChart`: lem:cha-PCcoord (coordinate `zeta`, `mu_0` with `pi mu_0 = S_0`, shifts `mu_{2r}`; thm:smo-MPS, thm:smo-TPC, thm:smo-WT2), turning-point-free coordinate eq:tha-YLsoft (prop:cha-halfrow (b)),
   thm:cha-PC (two-patch chain `valid`, forbidden-overlap transfer (S3) after thm:eng-volterra), identification of weights `W1_def`..`M2_def`.
4. `BulkPhaseInputs`: lem:smo-bulkphase (4) (DLMF 12.10.35 + Stirling), lem:smo-S0, regularity `C^{2M+1}` in `(X,t)` through the collisions (thm:smo-BSr, lem:smo-budget (e)).
5. `TransferBundle` (`TransferInputs` of all charts): app_thmB "(I2) and the changed coefficient", "(I2): soft charts"; lem:smo-budget (b)-(e), lem:cha-weber-coord (3), lem:cha-PCcoord (2), lem:tha-collar (2); parity eq:thb-parity.
6. `ChartInputs` geometry: `cover_bulk` (finite cover by blocks, compactness), `overlap_match`, `mirror_*` (symmetry of the mirror and gauge charts), `cover` (band covered by bulk blocks and soft windows).

## FINDINGS (paper statements made precise or corrected in the freeze)

* **F-geom** lem:tha-geom (c) (a single oscillatory overlap `[c', c]` for all `X` in a compact `J`) is false when `u_c^+ < u_c^-` (`sup_J u_- > inf_J u_+`); true per block of a finite cover.  prop:tha-W / thm:A(ii) must be per block (`ChartInputs.nb, lo, hi`).
* **F-A1..A7, F-B1..B5** in the docstrings of `TheoremA/Statements.lean` and `TheoremB/Statements.lean`: quantifier order (constants before `mu`), explicit vectors (not existential), case split by the value of `X_k`, labels equal indices, `OrdConnected` in lem:tha-count,
  `def:thb-inputs` incomplete (host/submatrix, parity, matching, common `q`), uniformity in `mu` hidden by `thm_B_conditional`, `h <= t0`, `log(1/h)` at even `m+1`.
* **F-loc** (H2), (H3) are required pointwise in `mu`; uniform margins are claimed "by compactness and continuity" -- needs `IsCompact K` and joint continuity of the jets (`JetReg`); to be checked in L2.G3 whether continuity in `C^2` suffices (it does by lem:hyp-morse openness).
* **F-DLMF (closed, round 2)** the signs of DLMF 12.8.6-7 in `shift_V_*` (and 12.2/12.8 recurrences, 12.10.18 connection `V(a,z) = Gamma(1/2+a)/pi (sin(pi a) U(a,z) + U(a,-z))`, Olver envelope constants) were checked numerically with mpmath (scratch, not committed) on a grid of `a, z`; all fields of `ParabolicCylinderFacts` are consistent with them (audit section of `Charts/ParabolicCylinder.lean`).
* **F-B-eps5** `OneStepInputs.G1_col` has `C h^{m+1} log(1/h)` for both parities; weaker than the paper's `h^{m+1}` for odd `m` (harmless, `PropThaSpliceTwoOrders` states the sharp one).

## Round-2 audit findings (chart hypothesis structures; each is also recorded in the corresponding docstring)

Verdicts: `LadderData.Valid` sound (a `SymplecticLadder` for every `h` and `j` is satisfiable, e.g. the rotation ladder); `ParabolicCylinderFacts` sound (numerics, F-DLMF closed); `BulkWeberChart` **fixed**; `BulkPhaseInputs` sound (matches lem:smo-bulkphase (4)); `SoftEdgeChart` **fixed**; `TransferInputs` **fixed**; `ChartInputs` sound (with F-t0).

* **F-bw** `BulkWeberChart` left the weights `W`, `M` free (only bounded), so an envelope could be inflated on single rows; added `W_def`, `M_def` (weights = the Weber envelopes `Ewell(-(k+1/2)) |Y(u_k)/sqrt h|`, resp. with `Mbal`); `W_osc`, `M_osc` kept as redundant consistent fields.
* **F-se** `SoftEdgeChart` lacked parts of lem:tha-geom (d) and of the chart's own definition: added `ucη_in` (collar `[u_c - 2 eta, u_c + 2 eta]` inside `(0,L)`), `geom_far` (away from `u_c` by `eta/4` and `|X - X_s^+| <= delta_0`: `T < 0`, `X - B_0 > 0`), `muS_bd` (`|mu_{2r}| <= C_mu`), `zeta_far` (`zeta^2 >= 4 max(mu_0,0) + c_z1` on `eta/4 <= |x| <= 2 eta`; the turning-point margin), and the constants `Cmu`, `cz1`.  Without them `SoftEdgeChart` was satisfiable by charts whose collar leaves `(0,L)` or whose `zeta` turns inside the collar.
* **F-ti** `TransferInputs.ulo, uhi` were *existential* inside the structure (a degenerate rectangle satisfied everything); they are now structure parameters, supplied by `TransferBundle` (bulk `[0, c + sigma/2]`, soft `[u_c -+ eta/2]`).
* **F-geom (corrected)** lem:tha-geom (c) is per block *and* the soft statements are per energy cover; **F-geom2** uniformity in `mu` also needs a *parameter* localisation (a neighbourhood `N in nhdsWithin mu_0 K` and a finite energy cover per neighbourhood, then compactness of `K`): `GeomMargins`; **F-geom3** the collision statement (a) at `u_c^+ = 0` or `L` is a statement about the mirror family at the right end (`GeomCollision`); **F-geom4** (d) for the lower soft edge goes through `negFamily` (`GeomSoftLower`).
* **F-t0** `t0` is chart data, `ChartInputs F K Kidx t0 ...`; the proofs of `ThmAii`, `CorThbDm` need a `ChartInputs.restrict` step (shrinking `t0`) that is not in the DAG; to be added to L2.C9.
* **F-E1..E4** (EigenvalueStatements): Step 0 is relative to the *frozen* band (`O(h^2)`); for the plain band it is `O(h)` (`StepZeroD0`); the interval `I'` of cor:eigen (b) needs `delta' <= delta`; counting needs `X_k` in the Lipschitz neighbourhood (Step 0); cor:eigen (c) first part needs only `x_0`.
* **F-B6 (cor:thb-Dm)** is not an instance of `ThmB` for `F`: the DM budget `r(2K+1)` exceeds `r(m)`, and the comparison is with the eigenvectors of `J_h`, not of the truncated `tilde J_h`; it needs cor:thb-stable, **absent from the DAG** (new row L3.D).
* **F-recheck** quantifier order, eigen-system universality, index ranges re-checked for prop:tha-W, prop:tha-W2 (clause (3) label = index verified against app_thmA Step 6; `lem:tha-M`'s `s_A`), lem:tha-win/M, thm:smo-spec, thm:A, prop:l2jets, prop:tha-splice, lem:tha-Mflat, lem:tha-collar, prop:thb-inputs, thm:B: no change needed beyond F-t0.
* **Not done**: a toy instance of the Setting structures (the spin family `G = 1, B = 0, L = 1`) was not formalised; hand check: `Xsp = 1`, `Xsm = -1`, allowed set `[(1 - sqrt(1-X^2))/2, (1 + sqrt(1-X^2))/2]`, `f_+'' = -4` at `1/2`, so (H1)--(H3) hold and `DM`, `EK` hold for all `M` (jets constant).

## Parts of the plan I am unsure about

* Whether `LadderData.Valid` is the right granularity: the window ranges (`max (jj (p-1)) 0 .. jj p + 1`) and `defect*` on `eqLo .. jj p` follow `volterra_multi`; L1.1 may force tightening of a range.
* `matchF`/`matchO`/`matchF_soft` (integral identities, `arccoshR` by logarithm) are the *definition* of the coordinates; their sign conventions at collisions (`SignType.sign (X - B_0(0))`) need a check in L4; they are not used by L2/L3 proofs except `turn_eq`, `Hz_lb`.
* `PropThaWin` omits item (4) (it is `ParabolicCylinderFacts.beyond`) and the Riemann-sum bounds (eq:tha-RiemannM, eq:tha-Riemanng) which are proof-internal; add them if L2.C4 needs them as lemmas.
* Satisfiability (see round-2 audit): no *Lean* toy instance of the chart structures (they mention the actual parabolic-cylinder functions; a degenerate `LadderData.Valid` instance needs a rotation ladder defined for all real `h`).
