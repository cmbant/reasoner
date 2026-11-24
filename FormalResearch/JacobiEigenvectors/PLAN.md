# Paper J (Jacobi eigenvectors): Lean plan

Paper: `Weyl/jacobi_eigenvectors/paper/` on QIprojects `main` (`92b28fb14`); corrections the Lean work triggered are in its `CORRECTIONS.md`. Label map: `THEOREM_MAP.md`; formalisation record: QIprojects `docs/lean_status.md`. Every headline theorem below depends only on `[propext, Classical.choice, Quot.sound]` (an axiom guard in its file); there are no `axiom`s and no placeholder proofs.

**Where it stands.** Layers 1–3 are proved modulo named chart inputs (Layer 4):
- `thmAii_proved` (thm:A (ii)) needs the chart data `ChartInputs` only;
- `thmA_of_layer4` (thm:A (i), (ii)) and `corEigen_proved` (cor:eigen) need the phase inputs `Layer4Inputs`;
- `thmB_proved`, `propThbInputs_proved` (thm:B, prop:thb-inputs) need the transfer bundle `TB`;
- `corThbStable_proved` needs `TB` and `EigGapBound`; `corFermions_proved` needs `TB`;
- `corThbDm_proved` (`rem:thb-Dm`) needs `TB` and `Layer4Inputs` of the truncated family.

`ParabolicCylinderFacts pcU pcV` holds unconditionally (`parabolicCylinderFacts`). No concrete chart exists yet, so every headline still takes a whole chart bundle as a premise, and no chart structure has a satisfiability witness.

**Theorem B route.** The paper proves thm:B twice: the public same-order seam proof (`sec:thb-proof`) and the next-order one-step proof (`thm:thb-onestep`, `prop:thb-inputs`, internal build). Both reconstruct the carriers by the two-row observation inverse `lem:thb-glue`, whose determinant is the engine's Casoratian over the bond coefficient. **Layer 3 formalises the one-step proof in its earlier form** (paper at `568de7144`): inputs (I2) transfer quotients (`t12`, `Ǎ = A^{[m+1]} - hB t11/t12` nonzero, Schur bounds on `1/Ǎ`, `B/(t12 Ǎ)`, `1/t12`, `t11/t12`), (I3) an exterior row, (I4) a mass set with a carrier-overlap inequality, and the ratio lemma (`jb_ratio`, `jb_glue`). The current criterion has (I2) = `lem:thb-glue` on each enlarged rectangle (at least two rows, one carrier pair `F = σ v y`, `F' = σ' v' y` for both orders, Schur norm of `v - v'` at most `C h^m`), no exterior row, (I3) = `‖F' e_k‖ ≥ c_0`, and no carrier-overlap condition. Its statement (`h_1` depending only on `m` and the input constants) and conclusion are those of `thmB_proved`. *Track B* below is the public proof.

**Layers and layout.** L1 engine (`Engine/`); L2 Theorem A (`TheoremA/`, `Assembly/`); L3 Theorem B (`TheoremB/`, using the separate umbrella `FormalResearch.JB`); L4 chart and special-function inputs (`Charts/`). Namespace `FormalResearch.JacobiEigenvectors.<Sub>`. The topic umbrella `FormalResearch.JacobiEigenvectors` is built on its own (`lake build FormalResearch.JacobiEigenvectors`), not imported by `FormalResearch.lean`. The structure files of the statement freeze are `Setting/JacobiFamily.lean`, `Charts/{LadderChain,ParabolicCylinder,BulkWeber,SoftParabolicCylinder,TransferCoefficients,ChartInputs}.lean`, `TheoremA/{Statements,GeometryStatements,EigenvalueStatements}.lean` and `TheoremB/{ComparisonMatrix,Statements}.lean`; the paper's statements are refined there, each refinement explained in the docstring.

## Proof obligations

Status: **proved** = Lean theorem with an axiom guard, under the hypotheses its docstring lists. Premises are those beyond the paper statement's own.

| id | paper | status | Lean (file) | remaining premise |
|---|---|---|---|---|
| L1.1 | thm:eng-volterra, per-patch ladders | proved | `LadderData.stability` (`Engine/LadderStability.lean`) | `Valid` (incl. (S3) `transfer`) |
| L1.2 | thm:eng-corr | proved, correctors as data | `eng_corr*`, `localized_eng_corr*` (`Engine/Corrector*.lean`) | correctors (`prop:eng-corr1`) are data (`adj_Pi` for the Weber ladder: `weber_adj_Pi`) |
| L1.3, L1.4 | setting; lem:eng-abel | proved | `exists_eigenSystem`, `eigVec_JacSol`, `bondA_pos`; `green_*` (`Setting/`, `Engine/Green.lean`) | none |
| L2.G | lem:hyp-morse, sec:tha-standing, lem:tha-geom | proved (per block, per parameter neighbourhood) | `hypMorseEquiv`, `hypOpen`, `frozenStandard`, `theGeometry` (`TheoremA/Geometry*.lean`) | none |
| L2.C1–C3 | prop:tha-W, lem:tha-win | proved | `propThaW`, `propThaWin` (`TheoremA/Bulk*.lean`, `WindowEnvelopes.lean`) | `BulkWeberChart`; `ParabolicCylinderFacts` |
| L2.C4 | lem:tha-M | proved | `propThaM_of_facts` (`TheoremA/WindowMass*.lean`) | soft chart field `corr_PC` |
| L2.C5 | lem:tha-count | proved | `propThaCount` (`TheoremA/Count.lean`) | none |
| L2.C6, C7 | prop:tha-W2 (1)–(4) | proved | `propThaW2_proved` (`TheoremA/SoftW2Proved.lean`) | `SoftMirror`, soft chart pair |
| L2.C8 | app_thmA Step 0 | proved | `stepZero`, `stepZeroD0`, `spectrumCovered` (`TheoremA/StepZero*.lean`) | none |
| L2.C9 | thm:A (ii) | proved | `thmAii_proved` (`Assembly/ThmA.lean`) | `ChartInputs` |
| L2.S1–S7 | lem:smo-bulkphase, thm:smo-spec, lem:smo-SM, thm:A (i) | proved | `bulk_*`, `smo_SM`, `smo_unique`, `smo_extend`, `thmAi_assembled` (`TheoremA/`, `Assembly/ThmAi.lean`) | `Layer4Inputs` |
| L2.E | cor:eigen (a)–(d) | proved | `corEigen_proved` (`Assembly/CorEigen.lean`) | `Layer4Inputs` |
| L2.J | prop:l2jets | **open** (E–M, roadmap) | `PropL2Jets` (statement only) | — |
| L3.1–L3.4 | prop:tha-splice (a)–(c), lem:tha-Mflat, lem:tha-collar (the current lemma is item (1); `propThaCollar_proved` also has the transfer bounds of the earlier item (2), which only the formalised criterion uses) | proved | `propThaSplice{Bulk,Soft,TwoOrders}_proved`, `propThaMflat_proved`, `propThaCollar_proved` (`TheoremB/`, `TheoremA/SoftMflat2.lean`) | `ParabolicCylinderFacts`, `SoftMirror` |
| L3.5 | prop:thb-inputs (internal; earlier inputs, see *Theorem B route*) | proved | `propThbInputs_proved` (`TheoremB/ThbFinal.lean`) | `TB` |
| L3.B | thm:B (one-step route) | proved | `thmB_proved` (`TheoremB/ThbFinal.lean`, `ThmBProof.lean`) | `TB` |
| L3.D | cor:thb-stable | proved | `corThbStable_proved` (`TheoremB/CorThbFinal.lean`; Fourier multiplier `χ(x)/x`) | `TB`, `EigGapBound` |
| L3.F | cor:fermions | proved | `corFermions_proved` | `TB` |
| L3.Dm | rem:thb-Dm (internal; was cor:thb-Dm) | proved | `corThbDm_proved` | `TB`, `Layer4Inputs` of the truncated family |
| — | cor:thb-scalar, lem:thb-hilbert, public proof of thm:B | not formalised | — | roadmap (matrix lemmas, Track B, Phase VI) |


## Roadmap


Phases, in order; each ends in a theorem that consumes the previous one.

1. **Phase I: consolidate WP0–WP2 (E–M).**
   (a) **Close the audit gaps** (`LAYER4_REMAINING_SCOPE.md`, *Status*). Done: `adj_Pi` for the Weber ladder for all `u, h` (`weber_adj_Pi`), the PC ladders of the actual pairs (`pcMinus_symplecticLadder`, `pcSwap_symplecticLadder`). Done: constants uniform over a compact set of `(μ, X)` (`localized_eng_corr_uniform`, from `Analysis.uniform_bigO_of_pointwise`; input: joint `C^{m+1}` regularity of the defect in `h`, a chart regularity field). Remaining: add the missing chart fields the `_of_corr` lemmas need, each a fact the paper uses: an upper bound on `Y` for the soft chart, a `corr_lead`-type field for `chainW`, the one-step ratio `A_{k+1} <= (1 + C h) A_k` of `AA 2`, regularity in `X` of `Y`, `zeta`, `mu_{2r}`; re-derive the lower bound on `lamL`'s denominator from those fields (not from `soft_lamL_lower`, which takes a whole chart).
   (b) **Core structures.** Split each chart structure into the data plus the fields that need new analysis (coordinates `Y`, `zeta`, `mu_{2r}`; correctors and their bounds) — `BulkWeberCore`, `SoftEdgeCore` — and prove constructors `BulkWeberChart.ofCore`, `SoftEdgeChart.ofCore`, `ChartInputs.ofCore` that derive every other field from the WP1/WP2 lemmas (exact ladders, envelopes, `W_mono`, `theta_le`, `W_osc`/`M_osc`, `seed_pos`, `collar_lb`, `bondA_le`, `grow_gap`, `ratioM`, `ratio2`, `grow3`, `lb_pc`, `lamL_cont`, cover, mirror). Headline theorems keep their statements; add `thmAii_of_core` etc. Exit: the residual premise of each headline is the core bundle only, and the redundant fields are lemmas (scope §4 items 3, 4).
   (c) **Finite-cover gluing** (F-geom2, scope §4 item 5): the theorems on a compact `K` from charts on finitely many parameter neighbourhoods `K'_α` (`local_cover_of_geom` gives one `K'` with its own `t0, Jlo, Jhi`); fix the order of choices (soft `delta0` before the cover widths) so it is not circular, and a restriction of `SoftPhaseInputs` to smaller `t0` (`softPhase_bandHi_close`).
2. **Phase II: coordinates (H).** WP3a (`Y_L`, turning-point free, ~250 lines) first, as the template; then WP3b (bulk `Y` through the hard-edge collision `X = B_0(0)`, ~700–1000 lines, the hardest single item); WP4 (`zeta`, `mu_0`, `mu_2`: Moser coordinate with two coalescing turning points). Paper constraints: `lem:cha-weber-env` (2) needs the `V_0 > 0` branch; `lem:cha-PCcoord` data only to their regularity order; `lem:cha-weber-coord` (3) only for `k <= floor(m/2)` .
3. **Phase III: first-order correctors (E–H) and Milestone M1.** For `m = 1` (`Kidx = 1`, shifts `mu_0`, `mu_2`) the correctors are explicit (`g_0 = V_0^{-1/2}`, `b_1` by one quadrature, `lem:eng-transport` with `q_V, W ∈ C^1`): derive `SymbolExpOn` from `(E_K)` and `C^3` of `Y`, `zeta`, build `LocalCorrectors`, and discharge `cas_lb`, `defect0/1`, `A_bd`, `B_bd`, `corr_lead`, `corr_PC` and the transfer regularity `reg_*`, `t12_lb`, `alpha_lb`. **M1: `thm:A` (ii) and `thm:B` (with `cor:fermions`) at `m = 1` with no chart premise** — the first non-vacuous end-to-end result, and the natural point to report Paper J as "formalised at first order". Route for thm:B at M1: the formalised one-step route needs `ChartPair` (`CI1` at order 2, i.e. the corrector `b_1` and the order-2 defect fields) and `TB` for both orders; `thm:A` (ii) at `m = 1` needs only `g_0`. First re-derive `propThbInputs_proved` from the current criterion in place (same name and guard, `TB` shrunk): it needs the `lem:thb-glue` determinant (the engine Casoratian, `Fcas`) and row variation instead of the transfer quotients `t12_lb`, `alpha_lb` and the exterior row, so `TransferInputs` loses those fields. Then build `CI1`. If building `CI1` costs more than Track B's remaining items, switch `thmB` to Track B, which needs only what `thm:A` (ii) needs plus the order-1 transfer data.
4. **Phase IV: eigenvalues at first order.** WP6a (`BulkPhaseInputs` at `M <= 1`: `lem:smo-S0` through the collision from `matchO` and WP3b, the Casoratian from `pc_phase_osc_lattice`; the paper derives the bulk phase (`lem:smo-bulkphase` (4)) from the complex Weber wave `w^{(1)} - i√(2/π) w^{(2)}`, DLMF 12.10.18–24, and its evenness in `h` directly from `C(-h) = conj C(h)` (`lem:tha-BS1` (2))) and `SoftPhaseInputs` at `M <= 1` (`bandHi_reg` by a `C^3` implicit function theorem, `muS_reg` for `r = 0`). Milestone M2: `cor:eigen` (a)–(d) and `thm:A` (i) at `M <= 1` unconditional.
5. **Phase V: all orders (VH; owner decision before starting).** `prop:eng-corr1` (corrector regularity `C^{p-3k}` through turning points and the collision, all `k`), `mu_{2r}` for all `r`, WP6b (all-order Hermite Plancherel–Rotach and the Stirling series). This is most of the remaining line count; M1 and M2 do not depend on it. `thm:smo-WT2` loses one parabolic derivative for `b` (sharp), none for the obstruction, and none for the weighted field `(x^2-α)b` when `λ > 1` (only `λ = 1, 3` are needed); the budget is `r(M) = max(14, 14⌈M/2⌉+9)`, with comparison class `C^{2K+3}` and frozen phase of order `j` in `C^{2M+1-j}`. The one-turn formula `b(x) = ∫_0^1 t^{λ/2−1} g(tx) dt` is the most Lean-friendly piece of `app:smooth`.
6. **Phase VI (optional; owner decision): `cor:thb-scalar`.** The scalar-sample eigenbasis (no matrix eigenvalues, residual `O(h^{m+1})`, absolute accuracy, canonical gauge; it supersedes `rem:thb-Dm`). Needs M2 (`cor:eigen` (b) samples), Track B (bulk seam with perturbed energies) and the soft chart at the exact Hermite order `a = −k − 1/2`, where the PC pair reduces to Hermite functions (`Special/Hermite*`). Not planned.

Independent of the phases (each standalone; none blocks M1):
* **L2.J** (`PropL2Jets`, E–M, ~150 lines): `thmAii_proved` for `truncFamily F m`, then `thb_stable_core` / `thb_jacobi_gauge` with `J_h` against `J̃_h` (gap from `eigGapBound_of_layer4`), as inside `corThbDm_proved`, plus `eq:l2-tildePsi`. Needs a `StdDM`-type weakening of the `DM` premise of `ThmAii` (F-DD1 pattern: the truncated family has `(D_m)`, not `(D_{2⌈m/2⌉+1})`), done in place: the same `ThmAii`/`thmAii_proved` with the weaker premise, no parallel copy.
* **Matrix lemmas of Theorem B** (E–M, pure matrix analysis; reusable, so in the shared `FormalResearch/MatrixAnalysis/`, not under `JacobiEigenvectors/`; search Mathlib and the vendored libraries first): the residual bound of `lem:thb-polar` (`‖JQ − QΛ‖ ≤ ‖JG − GΛ‖/σ_min(G)`, via the Sylvester identity `AS + SA = Q*R + R*Q`, ~150 lines); the elementary `lem:thb-residual` (row-square Schur bound, rectangular, perturbed `Λ̂`, ~150 lines; if adopted, re-derive `corThbStable` from it in place and delete `ThbStableMult`/`ThbStableSchur` once unused, as the simpler proof); `lem:thb-schur1` (one-sided variation; a special case of `jb_schur_of_C2` with no column derivative, ~80 lines).
* **Track B: the public same-order proof of thm:B** (M–H, ~2,000 lines; start only after the matrix lemmas). `lem:thb-hilbert` (weighted discrete Hilbert bound, `|β| < 1/2`, perturbed energies: Hilbert's inequality via Parseval on `AddCircle` for `∑_{l≠0} e^{ilθ}/l`, then rounding, dyadic blocks and the Schur test; ~500 lines); the matrix-level local defect `‖R_0‖ ≤ C h^{m+1}‖G‖` from the engine defect identity and `lem:thb-glue` at order `m` (shared with the re-derived `propThbInputs_proved`; ~400); the bulk seam bound from `propThaSpliceBulk_proved` and the Weber envelopes (~300); the soft seam weights `eq:thb-seam-weights` from the reflection `M_-(a)` (`reflect_V`, `pcSwap_eq_pcMinus`), `PropThaMflat` and derivative envelopes of the balanced pair (~600); absorption (~100). Payoff: `thmB` from **`CI0` and the order-`m` transfer data only**, with no `CI1` (order-`m+1` charts), no `ChartPair` and no order-`m+1` corrector; in the paper only `(E_{q_m/2})` with budget `r(q_m−1)` is used. Decide at the end of Phase III (below) whether to finish it. If it is finished, re-derive `thmB_proved` from it in place (same name, statement and axiom guard) and retire the one-step chain (`propThbInputs_proved`, `TB`, `ChartPair`, `CI1`) and its THEOREM_MAP rows; do not keep two headline routes. `lem:thb-hilbert` (Hilbert's inequality and its weighted form) also belongs in `MatrixAnalysis/`.
* Joint `ContDiff` of `(a, z) ↦ pcU, pcV` only if a Phase III consumer needs it (none known).

## Layer-4 inputs and the paper statements behind them

1. `ParabolicCylinderFacts` (DLMF 12.2.2, 12.2.4, 12.2.10, 12.8.2-3, 12.8.6-7, 12.2.15-16; Olver Ch.11 Thm 3.1, Ch.6 Thm 2.2): lem:cha-PCenv (1b), (2), (3); eq:tha-conn (`M_-(a)`).
   **Proved unconditionally for `pcU a z = Re U(a,z)`, `pcV a z = Re V(a,z)`** (`parabolicCylinderFacts` / `pcEnvelopeFacts` in `Charts/PCEnvelopeAssembled.lean`, after removing the unconsumed near-turning-point `V_growth` field from `PCEnvelopeFacts`):
   `PCExactFacts` (`Charts/PCExact.lean`), `PCSmoothFacts` (`Charts/PCSmooth.lean`), `PCPhaseFact` (`Charts/PCPhase.lean`), and `PCEnvelopeFacts` (`Charts/PCEnvelopeAssembled.lean`), plus far-zone growth `pcV_far_pos_and_growth` / `pcU_neg_pos_and_growth` in `Charts/PCVFarGrowth.lean`. (`ParabolicCylinderFacts.ofEnvelope` in `Charts/PCActual.lean` stays available for abstract `U, V`.)
2. `BulkWeberChart`: coordinate `Y`: prop:cha-halfrow (a), lem:cha-weber-coord (1)-(2), eq:tha-matchF/O; ladder (SM1)-(SM3) and annihilation: lem:cha-weber-ladder (1), (3), eq:cha-annih;
   envelopes and weights: lem:cha-weber-env (1)-(3), lem:cha-W0; `W_osc`, `M_osc`, `seed_pos`, `collar_lb`, `theta_le`; defect/Casoratian bounds `defect*`, `cas_lb`, `A_bd`, `B_bd`: thm:eng-corr + lem:cha-weber-coord (3) (this is L1.2, not Layer 4 proper).
3. `SoftEdgeChart`: lem:cha-PCcoord (coordinate `zeta`, `mu_0` with `pi mu_0 = S_0`, shifts `mu_{2r}`; thm:smo-MPS, thm:smo-TPC, thm:smo-WT2), turning-point-free coordinate eq:tha-YLsoft (prop:cha-halfrow (b)),
   `chainW` (Step 1, `cor:cha-I-general`), `patch1_eq`, `shared_PC`, `wf3_eq` (swapped pair), `W3_def`, `shape` (`P = 3`, switch bond `j_2`); (S3) of both overlaps stays in `valid` (`Valid.transfer`).
   thm:cha-PC (two-patch chain `valid`, forbidden-overlap transfer (S3) after thm:eng-volterra), identification of weights `W1_def`..`M2_def`.
4. `BulkPhaseInputs`: lem:smo-bulkphase (4) (DLMF 12.10.35 + Stirling), lem:smo-S0, regularity `C^{2M+1}` in `(X,t)` through the collisions (thm:smo-BSr, lem:smo-budget (e)).
5. `TransferBundle` (the only premise beyond the statements of `thmB_proved`, `propThbInputs_proved`, `corThbStable_proved` and `corThbDm_proved`, which also take the gap premise listed in the status table; `TransferInputs` of all charts): app_thmB "(I2) and the changed coefficient", "(I2): soft charts"; lem:smo-budget (b)-(e), lem:cha-weber-coord (3), lem:cha-PCcoord (2), lem:tha-collar (2); parity eq:thb-parity.
6. `ChartInputs` geometry: `cover_bulk` (finite cover by blocks, compactness), `overlap_match`, `mirror_*` (symmetry of the mirror and gauge charts), `cover` (band covered by bulk blocks and soft windows).

## Lean refinements of the paper statements

The paper's statements are refined in the freeze files as follows. Each refinement is explained in its docstring; the ID is the search key there.
- **Uniformity and localisation.** Constants come before `μ`, and uniformity needs `IsCompact K` and jointly continuous jets (F-A1..A6, F-loc). Geometry and charts are per energy block and per parameter neighbourhood (F-geom, F-geom2..4). `t0` is chart data with a restriction step `ChartInputs.restrict` (F-t0).
- **Explicit data.** Comparison vectors are explicit (`psiHatVec`, `envVec`), labels equal indices, and the relative clause of thm:A (ii) is a second conjunct (F-A(ii)-1).
- **Chart structures.** Fields were added so the structures cannot be satisfied degenerately: weights `W_def`, `M_def` (F-bw); the soft-collar geometry fields `ucη_in`, `geom_far`, `muS_bd`, `zeta_far` (F-se); `TransferInputs` rectangles as parameters (F-ti).
- **Soft chain.** The soft chain has three patches and a separate Step-1 Weber chain `chainW`, with `valid` for the rescaled chain (F-W2-1..3). Odd `m` is carried by the parameter `Lm` with `Lm_one`, `Lm_small` (F-W2-8). Further fields record facts the paper uses: `ratioM`, `bondA_le`, `grow_gap`, `collar_lbW`, `ratio2`, `clb`/`lb_*`, `lamL_cont`, `grow3`, `delta0_small` (F-W2-11, -18..-20, F-B5).
- **Theorem B.**
  - `SplicesInWindow` (open overlap) is a premise of the splice statements and of `ThmB` (F-B10).
  - Block choice is by least index, `blockIdx` (F-B11).
  - The right soft chart starts at the mirror fold row (F-CC1).
  - `StdDM` replaces `(D_{2K̄+1})` in `ThmB` and its corollaries (F-DD1).
  - The fermion constant is `8C h^m/τ`, for real matrices (F-FERM).
- **Parabolic cylinder functions.**
  - `phase_osc` holds on the lattice `μ² = 2n+1` (F-PC2).
  - Joint smoothness in `(a, z)` is weakened to slice smoothness plus joint continuity (F-PC3).
  - `V_growth` is restated, then dropped as unconsumed (F-PC1).
  - The DLMF signs were checked numerically (F-DLMF).

## Findings for the paper

Every statement-level finding from the Lean work is applied in the paper (QIprojects `main` `568de7144`), and the statement corrections are recorded in the paper's `CORRECTIONS.md`.
- Applied in the text: F-A1–A7, F-A(ii)-1, F-B1–B5, F-BB-1–3, F-E1–E4, F-geom, F-geom2, F-SM1, F-se, F-W2-9, F-W2-17, F-W2-19.
- Lean-only, because the paper works with actual functions and rows rather than abstract bundles: F-PW3, F-PW6, F-B10, F-B14, F-B15.
- Settled with no change: F-CC1. The chart starting at `n_c + 1` is correct; see the internal note in `app_thmB.tex`.

A new finding goes here as one row (ID, paper file and label, the problem, the fix). Once the paper is fixed, it moves to the lists above.


## Open design questions

- **Window ranges.** Is the granularity of `LadderData.Valid` right? Its window ranges follow `volterra_multi`, and building concrete charts may force a range to be tightened.
- **Coordinate definitions.** `matchF`/`matchO`/`matchF_soft` define the coordinates by integral identities. Their sign conventions at collisions (`SignType.sign (X - B_0(0))`) must be checked when WP3b builds `Y`.
- **Satisfiability.** No chart structure has a toy instance. The first will be the concrete charts of Phase III. Until then, satisfiability is supported only by the field-by-field audit in `LAYER4_REMAINING_SCOPE.md`.
