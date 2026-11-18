# Paper J, conditional pipeline: plan, dependency DAG, Layer-4 list

Status (round 4): the statement freeze of Layers 2--3 is in place and Layers 1 and most of the geometry, bulk and soft-edge (1) parts of Layer 2 are proved (table *Status of the proof obligations* below);
every theorem of the project closure has axioms `[propext, Classical.choice, Quot.sound]` only (checked by a scratch `collectAxioms` audit over all 1100+ theorems; no `axiom`, no placeholder proofs).
Paper: `Weyl/jacobi_eigenvectors/paper/parts/*.tex` on `origin/agents/m7-m1-global-racah` of QIprojects.
Layers: **L1** engine completion (`thm:eng-corr`, per-patch stability); **L2** Theorem A from engine + `ChartInputs`; **L3** Theorem B from L2 + chart inputs;
**L4** discharge the chart / special-function hypotheses (NOT this phase).  Namespace `FormalResearch.JacobiEigenvectors.<Sub>`.

Relocation notes (main session): the engine `FormalResearch/JE/` will move to `FormalResearch/JacobiEigenvectors/Engine/` (imports here are `FormalResearch.JE.*` until then);
`FormalResearch/JB/` (Theorem B reduction, `OneStepInputs`, `jb_onestep`, `thm_B_conditional`) stays and is to be folded into `TheoremB/` later.
`FormalResearch/JacobiEigenvectors.lean` is an umbrella stub, **not** in `FormalResearch.lean` yet.

## Status of the proof obligations (round 4)

Proved = a Lean theorem with an axiom pin, under the hypotheses stated in its module docstring ("Differences from the paper").  The names are those of the files.

| id | status | Lean name (file) | main restriction |
|---|---|---|---|
| L1.1 | proved | `LadderData.stability` (`Engine/LadderStability.lean`) | `Valid` (incl. (S3) `transfer`) is a hypothesis |
| L1.2 | proved under data | `eng_corr`, `eng_corr_full`, `eng_corr_site`, `transport_corrector`, `ex_eng_corr` (`Engine/Corrector*.lean`) | global domain `u in R`; `SymbolExp` (Taylor expansions) and the correctors with relations (a)_k, (b)_k are *data*; `nondeg` (bonds `D != 0` everywhere) excludes a hard-edge bond, so the theorem is **not applicable to the Weber ladder as it stands**: the chart fields `Valid.defect0/1` are not derived from it (Layer 4) |
| L1.3 | proved | `exists_eigenSystem`, `eigVec_JacSol`, `bondA_pos` (`Setting/EigenSystem.lean`) | `bondA_pos` needs `G_h > 0` at the nodes (hypothesis) |
| L1.4 | proved | `green_cas_const`, `green_cas_last`, `green_hasDerivAt` (`Engine/Green.lean`) | none |
| L2.G1--G3 | proved | `hypMorseEquiv`, `hypOpen`, `frozenStandard` (`TheoremA/Geometry.lean`) | none |
| L2.G4 | proved | `theGeometry` = (a) `geomBulk`, (b) `geomCollision`, (c) `geomMargins`, (d) `geomSoft`, `geomSoftLower` (`TheoremA/Geometry*.lean`) | none (statements of `GeometryStatements.lean`, per block / neighbourhood: F-geom, F-geom2) |
| L2.C1, C2 | proved | `bulkSolutionBound_of_one_le`, `bulk_conj1`, `bulk_collar_bound`, `propThaW` (`TheoremA/Bulk*.lean`) | `BulkWeberChart` fields; `m >= 1`, mirror overlap; `|kappa-hat| >= c` at eigenvalues only (F-C1..C3) |
| L2.C3, C4 | in progress (`TheoremA/WindowEnvelopes.lean`) | `PropThaWin`, `PropThaM` | |
| L2.C5 | proved | `propThaCount` (`TheoremA/Count.lean`) | statement has `1 <= N`, positive bonds (F-A7) |
| L2.C6 | item (1) proved | `propThaW2_item1`, `soft_through_edge`, `soft_valid`, `soft_pc_bound`, `soft_lamL_lower` (`TheoremA/Soft*.lean`) | `ParabolicCylinderFacts` and the new soft-chart fields (`bondA_le`, `grow_gap`, `collar_lbW`, `ratio2`, `ratioM`) |
| L2.C7 | `PropThaW2` (2)-(4): eigenvectors, quantisation (label = index), one shift short | prop:tha-W2 | C3, C4, C5, C6, C8 (Step 0), PC connection `M_-(a)` | 900 | VH.  **Not started in Lean (round 6: only the F-W2-8 refactor and the chain below)**.  Item (4) is items (1)-(3) for charts with `Lm = 1 + log(1/h)` (the `Lm` parameter of the charts, F-W2-8 applied): nothing separate to prove.  **Finding F-W2-12 (frozen `PropThaW2` was insufficient for (2),(3); APPLIED in round 6: `SoftMirror` in `Charts/SoftParabolicCylinder.lean`, a premise of `PropThaW2` and the type of `ChartInputs.mirror_up/lo`; the Step-0 premise `forall i, X_i <= bandHi + Cs0 h^2` with parameter `Cs0` on the eigen-system clauses (2), (3), matching `StepZero`)**: `CL`, `CR` are two independent charts of `Fz`, `mirrorFamily Fz`; (2) needs `a_R = a_L`, `Z_R(N-n) = -Z_L(n)`, `u_c^R = L - u_c^L`, same `eta, delta_0, N0` (the matching `psi-hat^L - kappa psi-hat^R` small on `Omega`, Step 4(b)), exactly the `ChartInputs.mirror_up` clause; the paper's proof uses it silently ("the mirror statement").  Minimal correction: a premise `SoftMirror CL CR := (forall p in P, CR.uc p = L - CL.uc p) /\ (forall p in P, forall alpha x, CR.zeta p alpha (-x) = -CL.zeta p alpha x) /\ (forall r p alpha, CR.muS r p alpha = CL.muS r p alpha) /\ CR.eta = CL.eta /\ CR.delta0 = CL.delta0 /\ CR.N0 = CL.N0` in `PropThaW2` (items (2),(3) only; (1) and the first half of (3) use `CL` alone; `ChartInputs.mirror_up` is the premise's instance).  **Second dependency**: item (2) needs `a <= a_+ = 1` at the eigenvalue, i.e. Step 0 (`StepZero`, L2.C8, unproved): either a premise `X <= bandHi + C h^2` or L2.C8.  **Chain (all with `Lm`; `CR` handled by the mirror, `psi^R_n := exact solution of the mirror recurrence at row N-n`)**: (E1, routine) `JacSol` uniqueness/existence on all rows `0..N` for `0 < bondA` (`exists_seeded`; uniqueness by the recurrence), eigen column `= psi^L/||psi^L||` (gauge `Psi_0 > 0`, `psi^L_0 = psiHatL_0 > 0`, `seed_posW`), and `psi^L = kappa psi^R` at an eigenvalue; (E2, routine) mirror transport of `JacSol` and of `psiHatL`, `lamL` (`CR.psiHatL` at row `N-n` equals `lambda_R psi-hat^{PC,+}`, `pcSwap`/`pcPlus` identities, `Z_R = -Z`); (E3, needs `PropThaWin` (C3)) envelopes on `Omega`: `|psi-hat^L| <= C |lambda_L| kappa^{-1} M`, `Molv ~ kappa^{-1} M` (weights in `[e^{-C}, e^C]`), (S4env); (E4, needs `PropThaM` (C4)) `||psi-hat^L||_Omega >= c |lambda_L| kappa^{-1} m_Omega^{1/2}`; (E5, routine given E3,E4) matching: `|kappa| ~ |lambda_L/lambda_R|`, `|kappa-hat - kappa| <= C h^m Lm |kappa|` (Cauchy-Schwarz), (S4mass); (E6, needs `Molv` envelope facts, `PropThaWin` (2)) tails (S4tail): PC sites beyond the Airy layer (monotone `f = E^2 M^2` + Riemann sum comparison + `int e^{-2S}/S'`), left Weber sites (`soft_f_growth`/`growth_ratio`: `psi_{n+1} >= (1+gamma) psi_n`, geometric sum, `Eminus` decay at `n_1 + 1`, `exp(-c_E/h)`), right Weber sites by the mirror; (E7, routine) normalisation `|Psi - hat Psi| <= C h^m Lm V/hat N`, `sum V^2 <= C hat N^2`, relative form (f); (E8) quantisation `|cos(pi a)| <= C h^m Lm` (`M_-(a)` connection at a right-forbidden site, `V_growth`, recessive-vs-growing comparison; excludes `0 < a <= C h` via convexity of `U(a,-Z)`); (E9, routine given `propThaCount`) counting: `Phi = pi mu~` strictly monotone (`mu0_deriv`), `sign D = sigma (-1)^k` at `a = -k` and `sign kappa' = sigma' (-1)^k` in window `k` (Casoratian at `Z ~ c eta h^{-1/2}` of `psi^L, psi^R`), `propThaCount` (i)-(iii) give existence/uniqueness per window and, with Step 0 and `IsEigenSystem` (`X_0 > ... > X_N`), label = index.  **Done (round 6, `TheoremA/SoftEigen.lean`)**: E1 (`rec_fwd_unique`, `rec_bwd_unique`, `eig_eq_normalised`, `eig_eq_kappa_mul`, `psiL_eq_kappa_psiR`), E2 (`jacSol_mirror`, `bandHi_mirror`, `aOf_mirror`, `Zof_mirror`), and the abstract l^2 lemmas of E5, E7 (`glueKappa_sub_le`, `normalised_error`); the instances of E5, E7 for the charts need E3, E4 (envelopes, masses).  Not done: E3, E4, E6, E8, E9.  Still to derive for E1 in the assembly: `0 < bondA n` for all `n < N` (from `A_ne_zero_rows` of the two charts, which cover all rows, or a premise).  Available inputs from C6: `propThaW2_item1` (apply to `CL` and `CR`), `soft_valid`, `soft_f_growth`, `soft_lamL_lower`, `pcSwap_eq_pcMinus` |
| L2.S4 | proved | `smo_SM` (`TheoremA/TruncationSM.lean`) | bounded jets `G_j` (F-SM1); one `mu`, no uniformity |
| L2.C8, C9, S1--S3, S5--S7, E, J | open | `StepZero`, `ThmAii`, ... | statements frozen |
| L3.* | statements frozen, reconciled with the paper of PR 250 (F-B7, round 4) | `TheoremB/Statements.lean` | not proved |

## Files of the freeze (all build; `lake build FormalResearch.JacobiEigenvectors`)

| file | content |
|---|---|
| `Setting/JacobiFamily.lean` | `SymbolFamily`, `jacobiMat`, `IsEigenSystem`, `JacSol`, `DM`, `EK`, `Hyp` (H1-H3), `frozenFamily`, `mirrorFamily`, `negFamily` (+ proved identities) |
| `Charts/LadderChain.lean` | `LadderData`, `.Valid` (engine hypotheses, eq:eng-UC1), `.Concl`, `.Stability` (statement of thm:eng-volterra for per-patch ladders) |
| `Charts/ParabolicCylinder.lean` | `k2, Mbal, Ewell, Ebar, kappaBal, Molv`; `ParabolicCylinderFacts` (DLMF 12.2/12.8, Olver envelopes, connection) |
| `Charts/Regularity.lean` | `BoundedC2`, `JetRegJ` (plain regularity bounds replacing lem:smo-budget) |
| `Charts/BulkWeber.lean` | `BulkWeberChart` (hard-edge Weber chart, per energy block), `BulkPhaseInputs` (lem:smo-bulkphase (4)) |
| `Charts/SoftParabolicCylinder.lean` | `SoftEdgeChart` (Step-1 Weber chain `chainW` + three-patch chain Weber / PC(`Z<=0`) / PC(`Z>=0`), validity of the rescaled chain), `pcMinus`, `pcSwap`, `Eminus`, `Eswap`, `aPC`, `lamL`, `psiHatL`, `pcSwap_eq_pcMinus` |
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
| L2.C6 | `PropThaW2` (1): through the soft edge, rescaling `lambda`, `|lambda_L| ~ lambda kappa_bal` | prop:tha-W2 (1), thm:cha-PC | L1.1 for the three-patch chain (rescaled), SE.valid/validW, PC (`reflect_V`, `molv_*`, `V_growth`) | 600 | VH. **Proved** (`TheoremA/SoftRescale.lean`, `TheoremA/SoftProof.lean`): `stability_rescale1`, `soft_weber_bound` (Weber bound on all rows `u <= u_c - eta/2`), `soft_through_edge` (`lambda > 0`, `|lambda_L| <= Lambda lambda kappa_bal`, pre-absorption PC bound on patch 2, engine bound on patch 3), `pcSwap_eq_pcMinus` (`M_-(a)`). **Item (1) proved** (`TheoremA/SoftProof.lean`, `SoftTransfer.lean`, `SoftAbsorb.lean`, `SoftWeights.lean`, `SoftOverlap.lean`, `SoftPC.lean`, `SoftGrowth.lean`, `SoftLower.lean`, `SoftItem1.lean`): `PropThaW2Item1` / `propThaW2_item1` (hypothesis `ParabolicCylinderFacts`; axioms pinned): R5 `Valid` split and `soft_valid` ((S3) derived), R1 absorption `Eminus_j1_decay`, R2 `soft_tail3`, R3 `molv_lower`, `soft_pc_bound`, R4 `soft_lamL_lower` (`growth_ratio`, `exists_seeded`, `soft_f_growth`), item-(1) assembly. New chart fields: `bondA_le`, `grow_gap`, `collar_lbW`, `ratio2`, `ratioM`. Item (1) is closed; L2.C7 (items (2)--(4)) remains |
| L2.C7 | `PropThaW2` (2)-(4): eigenvectors, quantisation (label = index), one shift short | prop:tha-W2 | C3, C4, C5, C6, PC connection `M_-(a)` (`reflect_V`, `pcSwap_eq_pcMinus`) | 900 | VH.  Inputs from C6: `propThaW2_item1` (`PropThaW2Item1`: `Cc, h0, clam, Clam`, Weber and PC bounds, `clam lambda kappa_bal <= |lambda_L| <= Clam lambda kappa_bal`; apply it to `CL` and to the mirror chart `CR`), `soft_valid`, `soft_f_growth` (the growth of the exact solution on `u_n <= u_c - eta/4` for the right Weber sites, `eq:tha-S4grow`).  Item (4) needs the `Lm` change of F-W2-8 first |
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
   Round 3 additions: `reflect_V` (DLMF 12.2.15--16, 12.2.7: `V(a,-z) = cos(pi a)/Gamma(1/2-a) U + sin(pi a) V`, the matrix `M_-(a)` of lem:cha-PCenv (1a)), `molv_well`, `molv_bar` (eq:cha-MolvEquiv, eq:cha-envbar: two-sided `M_Olv` equivalence, lower bound inside the well), `V_growth` (`V > 0`, `V' >= c_V k_2^{1/2} V` beyond the turning point; the ratio `r_2 < 1` of app_thmA Step 3 (ii)); numerically checked (mpmath, see `Charts/ParabolicCylinder.lean`).
   `ode`, `wronsk`, `shift_*` (lem:cha-weber-ladder (2)); `phase_osc` (DLMF 12.10.18, lem:smo-bulkphase (1)).  Needs a definition of `U, V` (none in Mathlib).
2. `BulkWeberChart`: coordinate `Y`: prop:cha-halfrow (a), lem:cha-weber-coord (1)-(2), eq:tha-matchF/O; ladder (SM1)-(SM3) and annihilation: lem:cha-weber-ladder (1), (3), eq:cha-annih;
   envelopes and weights: lem:cha-weber-env (1)-(3), lem:cha-W0; `W_osc`, `M_osc`, `seed_pos`, `collar_lb`, `theta_le`; defect/Casoratian bounds `defect*`, `cas_lb`, `A_bd`, `B_bd`: thm:eng-corr + lem:cha-weber-coord (3) (this is L1.2, not Layer 4 proper).
3. `SoftEdgeChart`: lem:cha-PCcoord (coordinate `zeta`, `mu_0` with `pi mu_0 = S_0`, shifts `mu_{2r}`; thm:smo-MPS, thm:smo-TPC, thm:smo-WT2), turning-point-free coordinate eq:tha-YLsoft (prop:cha-halfrow (b)),
   Round 3 (structure corrected, see the findings below): `chainW` (Step 1, `cor:cha-I-general`), `patch1_eq`, `shared_PC`, `wf3_eq` (swapped pair), `W3_def`, `shape` (`P = 3`, switch bond `j_2`); (S3) of both overlaps stays in `valid` (`Valid.transfer`).
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

## Round 3 findings (first proof attempt of `PropThaW2` (1), L2.C6; each checked against app_thmA Steps 1--3, charts.tex thm:cha-PC, engine.tex after thm:eng-volterra; details in `Charts/SoftParabolicCylinder.lean`)

* **F-W2-1 confirmed, fixed** (`valid` was for the unrescaled chain, forcing `lambda ~ 1`): `SoftEdgeChart.valid` is now `((chain).rescale1 lam).Valid`, `lam = softLamVal` (`E_Web(j_1)/E_-(j_1)`).
* **F-W2-2 confirmed, fixed** (two patches with weight `E_well(a,|Z|)` on all of `Z >> 0` fail `env`/`W_mono` for `a <= 0`; the paper has three patches, swapped pair `(v~,-u~)` with `E_well^{-1}` after `Z = 0`): the chain has `P = 3` for every `a` (patch 3 = patch 2 for `a > 0`), `pcSwap`, `Eswap`, `wf3_eq`, `W3_def`, `shared_PC`, `shape` with the switch bond `j_2`.
* **F-W2-3 confirmed, fixed** (Step 1 is a separate single-patch Weber chart on `[0, u_c - eta/2]`): `chainW` with `validW`, `shapeW`, `W_defW`, ...; `patch1_eq` identifies its Weber patch with patch 1 of `chain`; `psiHatL` takes the Weber part from `chainW`.
* **F-W2-4, F-W2-5 confirmed, fixed**: `PropThaW2` assumes `1 <= m` and `1 <= Lm h` on `(0,1]`.
* **F-W2-6 refined**: absorption follows from chart fields + definition of `Ewell` (not added); `eq:cha-MolvEquiv`, the growth of the dominant member and `V(a,-z)` (for `M_-(a)`) added to `ParabolicCylinderFacts` (`molv_well`, `molv_bar`, `V_growth`, `reflect_V`).
* **F-W2-7 refined, kept a field**: `Valid.transfer` is in `LadderChain.lean`; deriving it needs `bondA` bounds, `k_2 >= c/h`, one-step ratios of the weights; proposal: split `Valid` (without `transfer`) and add a lemma.
* **F-W2-8 (applied, round 6)**: item (4) (odd `m`, `q = m - 1`, `Theta <= C log(1/h)`, defect weights `rho_k != 1`) was not representable (`rho_one`, `theta_le` fixed `rho = 1`, `Theta <= Csum`).  Now `SoftEdgeChart F P m q U V Lm` has the parameter `Lm : ℝ → ℝ`; `theta_le`/`theta_leW` read `Theta <= Csum * Lm (step N)`; `rho_one`/`rho_oneW` are deleted; two chart fields about `Lm` were added that the first proposal missed: `Lm_one` (`1 <= Lm` on `(0,1]`) and `Lm_small` (`h Lm(h) -> 0`; otherwise there is no smallness threshold: for `Lm = h^{-10}` the statement is false).  `softH0`, `softHε` are built from `softHL ε` (a threshold with `h Lm(h) <= ε`); `soft_through_edge`, `soft_pc_bound`, `soft_weber_bound` now carry `h^m Lm(h)`; `propThaW2_item1` has no `Lm` argument (it is the chart's).  `ChartInputs` and `TheoremB/Statements` use `Lm = fun _ => 1`; `PropThaW2`, `PropThaWin`, `PropThaM` take `{Lm}` implicitly from the charts.  Consequence for other agents: every `SoftEdgeChart Fz P m q U V` must become `SoftEdgeChart Fz P m q U V Lm` (add `{Lm : ℝ → ℝ}` to the `variable` line).
* **F-PW3, F-PW4 (round 6, from the `PropThaWin` attempt)**: `PropThaWin` now takes `(cPC CPC : ℝ)` and has `ParabolicCylinderFacts U V cPC CPC →` as its first premise (item (3), the envelopes of `pcPlus`/`pcMinus` for all `z`, `C1` uniform in `a`, is false for arbitrary `U V`; the chart fields constrain them only at chain rows); `SoftEdgeChart.switch_in` (new field) puts `jj 2` and `jj 2 + 1` in `[0, N]` and in the collar `|u - u_c| <= 2 eta`, so the window `Omega` is non-empty (5a).
* **F-W2-11 (round 5, L2.C6)**: the lower half of (c) needs the paper's `M^2_Web ~ h^{1/2}` at the overlap rows as an input: new chart field `ratioM` (`M_{j_1+1} <= C_M M_{j_1}`); `r_W >= 1 + gamma/2` is derived from the exact solution (`growth_ratio`, `exists_seeded`) and the engine bound for patch 1, not from the corrector bound of `phi^{(1)}_1` alone.  Paper gap: `a <= a_+` is not assumed in `PropThaW2`; `muS_bd` (`r = 0`) is used for `|mu_0| <= C_mu`.  `PropThaW2` has no `ParabolicCylinderFacts` hypothesis; `propThaW2_item1` takes it.
* **F-W2-9 (new)**: the PC bound of `PropThaW2` (1) is for `u_c - eta/2 < u_n` (the paper's `<=` overlaps the Weber range in one row where `psi-hat^L` is Weber by definition).
* **F-W2-10 (new)**: the soft chart pinned only the first Weber member `wf 1 0`; `wfW_eq` pins both.

## Parts of the plan I am unsure about

* Whether `LadderData.Valid` is the right granularity: the window ranges (`max (jj (p-1)) 0 .. jj p + 1`) and `defect*` on `eqLo .. jj p` follow `volterra_multi`; L1.1 may force tightening of a range.
* `matchF`/`matchO`/`matchF_soft` (integral identities, `arccoshR` by logarithm) are the *definition* of the coordinates; their sign conventions at collisions (`SignType.sign (X - B_0(0))`) need a check in L4; they are not used by L2/L3 proofs except `turn_eq`, `Hz_lb`.
* `PropThaWin` omits item (4) (it is `ParabolicCylinderFacts.beyond`) and the Riemann-sum bounds (eq:tha-RiemannM, eq:tha-Riemanng) which are proof-internal; add them if L2.C4 needs them as lemmas.
* Satisfiability (see round-2 audit): no *Lean* toy instance of the chart structures (they mention the actual parabolic-cylinder functions; a degenerate `LadderData.Valid` instance needs a rotation ladder defined for all real `h`).

## Round 4: adversarial audit of rounds 2--3 and reconciliation with the paper of PR 250 (`origin/agents/m7-m1-global-racah`, after `401fb1893`)

**Reconciliation of Layer 3.**  The paper edits since the freeze that touch Layer 3 (`thmB.tex`, `app_thmB.tex`; `thmA.tex`, `app_thmA.tex` changed only in proof text and one remark) are: lem:tha-collar (1) has the bound `C e^{-c/h}` *without* `h^{-K}`
(`PropThaCollar` has no `Kx`; `PropThbInputs` has no `K_eps`: `eps5 <= C_eps e^{-c_eps/h}`); (I5) is "remaining rows" (`||Q_{0,Sigma}(G^[m] - G^[m+1]) P_Sigma|| <= C h^m`, vacuous for bulk blocks; outside the collar the column coincides with `hat Psi`), and
`JB.OneStepInputs.outside` (entries of `G0, G1, U` outside the used rows `<= eps5`) is stronger than that and is still what lem:tha-collar (1) gives, so `JB` is unchanged; (I1) is "columns and reference" (operator bound for `G^[m+1]`: follows from the
column bounds `OneStepInputs.G1_col` by the Frobenius estimate done in `jb_onestep`); (S1) blocks and remaining rows (`OneStepInputs.cols/ch/outside`); the constant `K` is `K_S` (`OneStepConsts.K`); the lower soft edge is `D_-` times the upper-edge column of
`-D_- J D_-` = `negFamily` at `-X_k` (`compColumn`; the model pair carries `(-1)^n`, so `(t_11, t_12) -> (-t_11, -t_12)`, which changes no Schur norm, `alpha`, `t_11/t_12` or `eq:thb-parity`; `TransferBundle.softLo*` are the transfer inputs of the `negFamily` chart itself);
`a = -(k + 1/2) + O(h^m log(1/h))` (logarithm only in prop:tha-W2 (4)) is used only in the proof of lem:tha-Mflat.  Rechecked, no change needed: `ThmB`, `CorThbDm` (matches cor:thb-Dm: `G^jet_m` from `tilde X_k` of the truncated family, `D_m` only),
`PropThaSpliceBulk/Soft/TwoOrders`, `PropThaMflat`, `StepZero*`, `SpectrumCovered`, `CorEigen*`.  The `SoftEdgeChart` parameter `Lm` (F-W2-8) enters Layer 3 only as `fun _ => 1`.

**Verdicts (Lean statement against the paper).**

| item | verdict | note |
|---|---|---|
| `eng_corr`, `eng_corr_full`, `eng_corr_site` | faithful, weaker | global domain, `SymbolExp`, correctors with (a)_k, (b)_k as data (not circular: the recursion refers to the ansatz `(Aans g k, Bans b (k-1))` / `(Aans g k, Bans b k)`, which excludes `g_k`; instance `ex_eng_corr` is non-vacuous); `nondeg` excludes the hard-edge bond (see L1.2 row) |
| `LadderData.stability` | faithful | no change of statement; docstring updated |
| `Green.lean` identities, `PropThaCount` | faithful | positivity of bonds and `1 <= N` are needed (F-A7) |
| `IsEigenSystem`, `exists_eigenSystem`, `eigVec_JacSol` | faithful | gauge `(Psi_k)_0 > 0`, order decreasing |
| `TheGeometry` (a)--(d) | faithful (per block, per neighbourhood) | F-geom, F-geom2 |
| `propThaW` | faithful with corrections F-C1..C3 | `N-hat`, `kappa-hat` bounds stated for every `X` (stronger than the paper, which says "at an eigenvalue"); `|kappa-hat| >= c` only at eigenvalues |
| `smo_SM` | faithful, needs one more hypothesis | F-SM1 |
| `propThaW2_item1` + new chart fields `ratioM, bondA_le, grow_gap, collar_lbW, ratio2` | faithful | each is a fact the paper proves or uses in Step 3 (`ratioM`: "`M^2_Web ~ h^{1/2}`"; `grow_gap`: `Q_0 - 2 sqrt(E_0) >= nu` on the compact `[0, u_c - eta/4]` plus `O(h^2)`, derivable from lem:tha-geom (d) and `(E)`; `bondA_le`: bounded `G_h`; `collar_lbW`: lem:cha-W0; `ratio2`: Step 3 (ii) `r_2 <= 1 + O(h)`), none is a conclusion in disguise, and they are mutually consistent; four of them are derivable from `Hyp` and `EK` and are fields only to keep the chart structure self-contained |
| Layer-3 statements | faithful after F-B7 | `PropThaCollar`, `PropThbInputs` strengthened to the paper's form |

## Findings for the paper (consolidated; label, what is wrong or missing, minimal corrected statement)

| label | location | what is wrong / missing | corrected statement |
|---|---|---|---|
| F-corr1 | `app_engine.tex`, proof of (b)_k of thm:eng-corr | "`F_cas = c_0 + ... + c_{2k} h^{2k} + O(h^{2k+2})` is even, so its centred difference is `O(h^{2k+3})`": a bare `O(h^{2k+2})` remainder has centred difference `O(h^{2k+2})` | "`F_cas = sum_{i <= k} c_{2i} h^{2i} + h^{2k+2} f(s) + O(h^{2k+3})` with `f in C^1`; by evenness the remainder is `O(h^{2k+4})`, so the centred difference is `h^{2k+2}(f(s + h/2) - f(s - h/2)) + O(h^{2k+4}) = O(h^{2k+3})`" (equivalently: `B^tot` is odd in `h` (thm:eng-defect (2)) and `O(h^{2k+2})`, hence `O(h^{2k+3})`; this is the route formalised in `Engine/Corrector.lean`, `D1_lift`) |
| F-SM1 | `app_thmA.tex`, lem:smo-SM | "real `G_j, B_j`" is not enough: `G_0 = 1`, `M = 1`, `G_1 = -c/(s - L/2)` (`c > 1`) gives a negative `E_n` at the node `L/2 + h` for infinitely many `h` | add "with `G_j` bounded on `[0, L]` for `j <= M` (automatic under `(D_M)`)" |
| F-geom | `thmA.tex`, lem:tha-geom (c) | one pair `c' < c` for all `X` in a compact `J` is false when `u_c^+ < u_c^-` (`sup_J u_- > inf_J u_+`) | "for every compact `J` and every `mu_0 in K` there are a neighbourhood `N` of `mu_0`, finitely many closed intervals `J_nu` covering `J` and `c'_nu < c_nu`, `delta_1 > 0` with `u_-(X) + delta_1 <= c'_nu < c_nu <= u_+(X) - delta_1` for `X in J_nu`, `mu in N`" (the uniformity in `mu` also needs the localisation of sec:tha-standing: F-geom2) |
| F-A7 | `app_thmA.tex`, lem:tha-count | false without `N >= 1` and `a_n > 0` for `0 <= n < N` (all bonds zero) | add "`N >= 1`, `a_n > 0` for `0 <= n < N`, `I` an interval" |
| F-W2-9 | `thmA.tex`, prop:tha-W2 (1) | the PC range `u_c - eta/2 <= u_n` overlaps the Weber range `u_n <= u_c - eta/2` in one row, where `psi-hat^L` is Weber by definition | PC bound for `u_c - eta/2 < u_n <= u_c + 2 eta` |
| F-W2-11 | `app_thmA.tex`, Step 3 | uses `a <= a_+` / `|mu_0| <= C` without stating it | "`|mu_{2r}(X)| <= C_mu` for `|X - X_s^+| <= delta_0`" (from the chart) |
| F-t0 | `thmA.tex` (standing/freezing), thm:A(ii), thm:B | the frozen family is a chart family for `|t| <= t0` and `t = h` must lie in it | "for `0 < h <= min(h_m, t_0)`" |
| F-E1 | `app_thmA.tex`, Step 0 | `X_k in [X_s^- - C h^2, X_s^+ + C h^2]` holds for the band of the *frozen* principal symbols `G_0 + h G_1` (`O(h)` from the band of `J_h`'s own `G_0, B_0`) | "`X_k in [X_s^-(h) - C h^2, X_s^+(h) + C h^2]`, `X_s^pm(t)` the band ends of `G_0 + t G_1`, `B_0 + t B_1`; for the plain band `O(h)`" |
| F-E2..E4 | `main_results.tex`, cor:eigen (b)--(d) | `I'` needs `delta' <= delta`; the counting sum needs `X_k` inside the Lipschitz neighbourhood (Step 0, `O(h)`); (c) first part needs only `x_0` | state `delta' <= delta`, the neighbourhood radius before `g`, and `x_0` only |
| F-A1..A6 | `main_results.tex`, thm:A | quantifier order (constants before `mu`), vectors explicit (not existential), case split by the value of `X_k`, labels equal indices, `C^{M+1}` through the collisions | as in the docstring of `TheoremA/Statements.lean` |
| F-loc | `thmA.tex`, sec:tha-standing | uniform margins "by compactness and continuity" need `IsCompact K` and jointly continuous jets (`JetReg`) | state both |

Lean-side only, not paper findings: F-W2-8 (the paper's prop:tha-W2 (4) already carries `log(1/h)` in (1)--(3); the Lean `PropThaW2` needed the `Lm` parameter to say so), F-C1..C3 (`m >= 1`, mirror overlap, `|kappa-hat| >= c` at eigenvalues: the paper states them for eigenvalues and `m >= 1`).
Resolved in the paper of PR 250 since the freeze (no longer findings): F-B1 (`def:thb-inputs` incomplete: host/submatrix structure, parity, matching are in (S1)--(S3) and "Charts, bootstrap blocks"), F-B-eps5 / (I1) (operator bound for `G^[m+1]` from the column bounds), F-B6 (cor:thb-Dm now via cor:thb-stable),
`h^{-K}` in lem:tha-collar and (I5) (now `C e^{-c/h}` and "remaining rows"), `D_-` for the lower soft edge, `s, t != 0` in lem:thb-ratio (now `delta < c_0` forces it).
