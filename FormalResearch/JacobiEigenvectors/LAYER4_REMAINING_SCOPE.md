# Layer 4 remaining inputs: status and scoping note

## Status

WP0–WP2 were written by an external agent (agy) and merged to `master` in `b90b43f` (imported by `FormalResearch/JacobiEigenvectors.lean`; no placeholder proofs, custom axioms or `native_decide`). A clean-context read-only audit (2026-11-23, nothing rebuilt) found what follows. The roadmap that acts on it is in `PLAN.md`, *Roadmap*. The scoping report below it is the original agy run, kept for its field-by-field routes; where it and this section disagree, this section is current.

**Proved and complete.** WP0a: `V_growth` removed from `PCEnvelopeFacts`; `pcEnvelopeFacts`, `parabolicCylinderFacts` (`Charts/PCEnvelopeAssembled.lean`) take no hypothesis, so `ChartInputs.pc` is available for `pcU, pcV`. Far zone: `pcV_far_pos_and_growth`, `pcU_neg_pos_and_growth` (`Charts/PCVFarGrowth.lean`).

**Consumed by the cores.** `BulkWeberChart`, `SoftEdgeChart` extend `BulkWeberCore`, `SoftEdgeCore`; `BulkWeberChart.ofCore`, `SoftEdgeChart.ofCore`, `ChartInputs.ofCore` derive the fields marked *derived* below, and `thmAii_of_core`, `thmB_of_core`, `corFermions_of_core` state the headlines for the charts of the cores (`Charts/*Core.lean`, `Assembly/HeadlinesOfCore.lean`). Verdict per lemma (target field: status):
* `weber_symplecticLadder`, `weber_annih` (patch-1 `valid.ladder`, `annih`): discharge once the chain is built from `weberPiP/PiM`, `wWeb Y`; they hold for every `Y` (no coordinate content). `weber_env_well` (`valid.env`, Weber patches): bulk modulo `Y_bound`; soft needs an upper bound on `Y` that `SoftEdgeChart` lacks.
* `pc_symplecticLadder` (patches 2, 3): **instantiated** for the actual pairs: `pcMinus_symplecticLadder`, `pcSwap_symplecticLadder` (`Charts/PCLadderBranches.lean`, no premise beyond the even shift).
* `localized_eng_corr(_full)` (`valid.defect0/1`): abstract engine only. `LocalCorrectors` (existence of the correctors, `prop:eng-corr1`) is assumed; `SymbolExpOn`, `langer` and `M0_smooth` are not proved; `adj_Pi` for the Weber ladder, including the hard-edge bond, is `weber_adj_Pi` (`Charts/WeberLadder.lean`; for the PC ladder `Pp_eq_adj_of_prod` applies, `Dp ≡ 1`); the `UOOn` constants are per fixed `(μ, X)`; `localized_eng_corr_uniform` (`Engine/CorrectorUniform.lean`) makes them uniform in a compact parameter set, given the joint regularity of the defect (a chart regularity input, `lem:smo-budget` (e)). Nothing addresses `cas_lb`, `A_bd`, `B_bd`, `W_mono`, `theta_leW` or the soft `theta_le`.
* `soft_bondA_le`, `soft_grow_gap`: **derived** (`bondA_le`, `grow_gap`; `SoftEdgeCore.exists_bonds`, from the standing assumptions `SoftEdgeCore.FamilyInputs`). `mirror_bulk_overlap_match`, `uMinus/uPlus_mirror_ne`: discharge (given `GeomSoftConcl` with matching `uc`, and the chart's `N0`).
* `bulk_W_osc_M_osc`, `bulk_theta_le`: **derived** (`W_osc`, `M_osc`, `theta_le`) from `turn_eq`, `Hz_lb`, `overlap_in_well`, `Y_bound` (coordinate fields, WP3b).
* `weber_seed_pos_of_corr`, `weber_collar_lb_of_corr`: **derived** for the bulk (`seed_pos`, `collar_lb`) and the soft chart (`seed_posW`, `collar_lbW`, `lb_weber`; the soft core has the new fields `Y_le`, `corr_leadW`).
* `soft_lb_pc_of_corr` (`lb_pc`), `soft_ratioM` (`ratioM`): **derived** (`lb_pc` from `corr_PC`; `ratioM` from the new core field `Y_le`).
* `soft_ratio2_of_corr`, `soft_grow3_of_corr`: **derived** (`ratio2`, `grow3`; the soft core has the one-step ratio field `AA2_ratio`).
* `lamL_continuousOn_of_coeff` (`lamL_cont`, still a core field): the `a = 0` cancellation is proved; it needs continuity in `X` of `AA 2`, `BB 2`, `zeta`, `aPC`, the Weber solution and the bond (the soft chart has no regularity fields for `Y`, `zeta`, `mu_{2r}`), and a non-vanishing denominator whose only source, `soft_lamL_lower`, takes a complete `SoftEdgeChart` (circular if used to build one).
* `local_cover_of_geom`, `local_bulk_cover_of_geom`: give a parameter neighbourhood `K'` with its own `t0, Jlo, Jhi`, not the fixed `K`. The finite-cover gluing is `Assembly/CoverGlue.lean` (`thmAii_of_local_charts`, `thmAii_of_local_cores`, `thmAi_of_cover`, `thmB_of_cover`); the choice order is the fixed one in its docstring (`delta0` of the soft charts first, then `delta_up = delta_lo = delta0`). `softPhase_bandHi_close` gives a new `t0`; `SoftPhaseInputs.restrict` restricts to a smaller `t0` and a subset of the parameters. `layer4_cover_consts`: packaging (its premise carries the content). `softMirror_geom_of_left`: transfers the left chart's coordinate fields to the mirror chart (no reduction of the (H) content).

**Housekeeping found by the audit:** done (axiom guards for `uMinus_mirror_ne`, `local_cover_of_geom_strict` and the `ODEFlow.lean` theorems; stale `V_growth` comments replaced by `pcV_far_pos_and_growth`).

**Statement audit of the Phase I Lean statements against the paper (independent read; verified items unless marked suspected).**
* `ThmAiiCover` took a separate chart witness in the absolute and the relative clause: fixed, one chart `pick mu` serves both (`Assembly/CoverGlue.lean`).
* `regBudget M` is `max{14, 14 ceil(M/2) + 9}`, the paper's `r(M)` before QIprojects PR 302 (which lowers it to `max{14, 9 ceil(M/2) + 9}`; see `PLAN.md`) (`Setting/JacobiFamily.lean`); the former `9M + 22` was stronger than needed: the proofs use at most `C^2` of the principal jets at this layer, and only the numerals in `StepZero.lean`, `BulkSlope.lean`, `ActionDerivativeDt.lean` changed. The umbrella builds.
* `ThmAi` omitted the clause of `thm:A (i)` that for `h <= h_M` every eigenvalue lies in `[X_s^- - delta, X_s^+ + delta]`: now `ThmAiFull` (`TheoremA/ThmAiLoc.lean`), proved from `ThmAi` by `thmAiFull_of_thmAi` through `stepZeroD0`. The statement that `S_j` depends only on jets of order `<= j` is still not stated (plan items L2.S7, L2.S8).
* `ChartInputs` fixes `Lm = 1` for all soft charts (confirmed mismatch, not a paper error). For even `m`, `ThmB`'s order-`(m+1)` chart `CI1` has `q = m`, one shift short; the paper only gives `Theta <= C log(1/h)` there (`thm:cha-PC` one-shift-short item, `prop:tha-W2 (4)`), while `CI1`'s soft `theta_le` demands `Theta <= C_sum`. `etaR` already carries the `log(1/h)`, so the statement is right but `CI1` asks for more than the paper proves, and `ThmB` for even `m` may rest on unsatisfiable inputs. Fix: give `ChartInputs` an `Lm` (with `Lm_one`, `Lm_small`) and use `1 + log(1/h)` for `CI1` when `m` is even, carrying `Lm` through the `TheoremB` soft-chart lemmas (about 20 files use the `fun _ => 1` charts). `m = 1` (milestone M1) is not affected. Open.
* `FermionConcl` is for real `F` and real projections only (paper: real or complex). Documented.
* `PropThaW` relative clause is stated on `delta`-collars only, the paper's `prop:tha-W (2)` is `delta`-free; `ThmAii`'s epsilon form needs only the collar form, and `BulkWeberChart.collar_lb` supplies the rest. Note.
* `FamilyInputs.geom` against `lem:tha-geom (d)`: same content; the paper now states the order of choices (`eta` first, `delta_0` decreasing). The paper's `J = [X_s^- + delta_0, X_s^+ - delta_0]` in `thmA.tex` is not a touching cover: the bulk blocks cover `[X_s^-(0) + delta_0/2, X_s^+(0) - delta_0/2]`, which overlaps the soft windows `|X - X_s^pm| <= delta_0` in length `delta_0/2 - O(t_0)`, matching Lean's strict `cover`; the `delta_0/8` cover of `app_thmA.tex` is the eigenvalue-rule proof, a separate choice. Checked, no change.
* Splices: Lean takes positions in the open overlap, the paper a row in the closed window; the paper now says positions with nearest row.
* Simplifications (suspected): `Y_le` is derivable from `matchF_soft` and `Y_forb`; the right and lower charts could be built from the left one, removing `overlap_match`, `SoftMirror` and the common `N0` bookkeeping; the `Hyp` conjuncts `a = 0 -> X = B_0(0)` are derivable.
* Paper imprecision for the Phase III correctors: `lem:cha-PCcoord (2)` does not state the uniform `C^{m+2}` bound and `g_0 >= g_- > 0` on the parabolic-cylinder collar that `AA2_ratio` uses (stated for the Weber chart only). To settle when the correctors are constructed.

**Paper check of the core fields added in Phase I:** the soft core's `Y_le`, `corr_leadW`, `AA2_ratio` are not new claims. They follow from facts the paper states: the coordinate `Z_0` is continuous with uniform constants on `[-sigma_1, U+sigma_1]` (`prop:cha-halfrow`), so `Y` is bounded on the Weber zone; the correctors exist, are bounded with their derivatives and the leading one is positive (`lem:cha-weber-coord` (3), `thm:eng-corr`), so `|AA 1 - g0| <= C h^2`, and the one-step ratio `A_{k+1} <= (1 + C h) A_k` is a Lipschitz bound with a positive lower bound. No paper error and no `CORRECTIONS.md` entry; the fields become lemmas when Phase II-III construct the coordinates and correctors. (Read from the statements, not re-derived from the appendix proofs.)

**Paper findings of the agy run (section 5 below):** 1 (`thm:eng-corr` needs `adj_Pi`, not `D² ≠ 0`) is applied in the paper (`Weyl/jacobi_eigenvectors/paper/CORRECTIONS.md`, 2026-11-19); 2 (`c <= u_+ - 2 sigma`) is a choice in the chart construction (the paper's margins `delta_1` already allow it), not a paper error; 3, 4 are remarks, no correction.

# Scoping Report: Remaining Layer-4 Formalisation for Paper J (`FormalResearch/JacobiEigenvectors/`)

Scoped on branch `lean/paper-j-layer4` in `/home/user/agy/scope_l4`.
All claims about Lean declarations, types, and proved status are **verified directly from the Lean source files** (no Lean toolchain was invoked). Numerical checks were performed with `mpmath 1.3.0` (`agy_scratch/check_weber_ladder.py`, `agy_scratch/check_t12_bulk.py`). Line-count estimates and routes for unproved `(H)` items are explicitly marked as estimates/inferences.

---

## Legend of Verdicts

* **(D)** Derivable by construction/definition once the chart is built concretely from `pcU`/`pcV` and the Weber/PC ladder.
* **(E)** Provable now from the proved envelope facts (`PCEnvelopeAssembled.lean`, `PCExact.lean`, `PCSmooth.lean`, `PCPhase.lean`, `PCLaplace.lean`, `PCEnvWellFar.lean`, `PCEnvBar.lean`) and existing `Engine/` / `TheoremA/` / `ThirdParty/lean-dlmf` infrastructure, with estimated Lean line count.
* **(H)** Hard new analysis (Langer/Moser coordinates, smooth dependence through turning points/collisions, localised all-order `prop:eng-corr1` + `SymbolExp`, all-order uniform asymptotics + Stirling), with cheapest honest route.
* **(X)** Blocked by an upstream-unproved theorem/assumption in the current frozen definitions.

---

## 1. Field-by-Field Verdicts

### 1.1 `BulkWeberChart` (`Charts/BulkWeber.lean`)

Concrete Weber ladder data for `(μ, X, N)` with matched coordinate `Y`, smooth extension `Yext` to `ℝ`, `h = F.step N`, `u_k = (k + 1/2) h`:
* `dd 1 s h' = Real.sqrt s`, `d2 1 s h' = s`, `ω 1 h' = Real.sqrt h'`
* `pp 1 s h' = Real.sqrt ((F.L - s) * F.Gh μ h' s)` (smoothly extended outside `[0, c + σ]`), `qq 1 u h' = X - F.Bh μ h' u`
* `wf 1 0 u h' = ![ut pcU (-u/h') (Yext u / Real.sqrt h'), Real.sqrt h' * kappaBal (-u/h') * deriv (pcU (-u/h')) (Yext u / Real.sqrt h')]`
* `wf 1 1 u h' = ![vt pcV (-u/h') (Yext u / Real.sqrt h'), Real.sqrt h' * Real.sqrt (Real.pi / 2) * (kappaBal (-u/h'))⁻¹ * deriv (pcV (-u/h')) (Yext u / Real.sqrt h')]`
* `PiP 1 u h' = T_gen (u + h') u h' 1 * S_+ (Yext u) (u + h'/2)`, `PiM 1 u h' = S_- (Yext (u - h')) (u - h'/2) * T_gen u u (-h') (-1)` where `S_±(y, s) = [[y/2, ∓1], [±(s - y²/4), y/2]]` and `T_gen c u h' sgn` is the fundamental matrix on `τ ∈ [0, 1]` of `dΦ/dτ = sgn * [[0, Yext'(u + τ h')], [(Yext(u + τ h')²/4 - c) Yext'(u + τ h'), 0]] Φ`.
* `W k = Ewell (-(k + 1/2)) |Y(u_k)/√h|`, `M k = Mbal (-(k + 1/2)) (Y(u_k)/√h)`, `ρ = ρt = 1`, `NR = ⌊c/h - 1/2⌋`, `jj 0 = 0`, `jj 1 = NR - 1`, `s0 = 0`.

| Field | Verdict | Justification / Route / Reuse |
|---|---|---|
| `cs, N0, c', c, σ, Csum, cM, CM, cH, c3, Y, Hz, chain` | **(D)** | Data fields (with `c', c, σ` from `Margins.geomMargins` on a localised `K' ⊆ K`). |
| `consts_pos` | **(D)** | Immediate from choice of positive constants (`σ = δ₁/2` from `geomMargins`, `c + σ < L`). |
| `overlap_in_well` | **(E)** (~40 L) | From `TheoremA/GeometryMargins.lean` (`Margins.geomMargins`), **provided `P = paramSet K' t0` is localised in `μ`** (`F-geom2`; see §3). |
| `turn_eq`, `Hz_lb`, `matchF`, `matchO`, `Y_bound` | **(H)** | Matched Weber–Langer coordinate `Y(u; X)` through the hard-edge collision `X = B_0(0)` (`prop:cha-halfrow (a)`, `lem:cha-weber-coord (1)-(2)`, `lem:smo-budget (b)`). Cheapest route: split into non-collision (`X ≠ B_0(0)`) via 1D IFT on `matchF`/`matchO` + analytic glue at `u_-`, and collision neighbourhood via Langer normal form `T(u) = (u - u_*) * ...` + `C^{r-2}` Hadamard/IFT in `(u, X)`. |
| `shape`, `A_bond`, `Q_diag`, `dd_sqrt`, `omega_sqrt`, `wf_eq`, `rho_one`, `W_def`, `M_def` | **(D)** | Hold directly from the concrete definitions above (`N0` large so `F.step N ≤ min σ (2 c)` and `0 < F.Gh` on `[0, c + σ]`). |
| `valid` — bookkeeping (`h_pos`, `P_pos`, `jj0`, `jj_mono`, `jj_last`, `s0_cases`, `omega_eq`, `A_eq`, `Q_eq`, `A_hard`, `D_hard`, `M_pos`, `W_pos`, `ρ_nonneg`, `ρt_pos`) | **(D)** | Immediate from definitions (`D_hard`: `Real.sqrt 0 = 0`; `A_hard`: `F.bondA μ N (-1) = 0`; `A_eq` uses `0 ≤ Gh` from `(H1)` + `(E_K)`). |
| `valid.ladder` (`SymplecticLadder`), `valid.annih` | **(E)** (~400 L) | **Provable now** from `PCExactFacts` (`pcExactFacts` in `Charts/PCExact.lean`), `pcSmoothFacts` (`Charts/PCSmooth.lean`), and `ODE.exists_linear_system` (`ThirdParty/lean-dlmf/DLMFMathlib/Analysis/ODE/LinearGlobal.lean`). `annih` follows from `pc_shift_U_up (-1/2) z` + `T_gen` preserving solutions. Verified numerically to `~1e-41` in `agy_scratch/check_weber_ladder.py`. |
| `valid.W_mono` | **(E)** (~80 L) | Provable from `matchF` + `turn_eq` + `Hz_lb`: for `u_k ≤ u_-`, the exponent of `Ewell` equals `(1/h) ∫_{u_k}^{u_-} arccoshR(|Q_0|/(2√E_0)) dv`, which decreases in `k`; for `u_k ≥ u_-`, `Ewell = 1`. Thus `CE = 1`. |
| `valid.env` | **(E)** (~100 L) | Provable from `PCEnvelopeAssembled.pc_env_well` (`env_well` on `z ≥ 0`), `PCExact.pc_reflect` & `pc_reflect_V` at half-integers `a = -(k+1/2)` (handling `Z_k < 0` when `X < B_0(0)`), and `h * k2(a_k, Z_k) ≤ C` from `Y` bounded. |
| `valid.cas_lb`, `valid.defect0`, `valid.defect1`, `valid.A_bd`, `valid.B_bd`, `corr_lead` | **(H)** / **(X)** | Blocked on `Engine/Corrector.lean` (`CorrSetting.nondeg` fails at `s = 0` for `d2 s h = s`, and `UO`/`PApprox` are global on `ℝ` without `SymbolExp` derivation or `prop:eng-corr1` regularity through turning points/collisions). Route: fix `CorrSetting` (use `adj_Pi` or localise to `[0, c + σ]`), derive `SymbolExp` from `EK` + `C^3` of `Y`, construct `g_i, b_i` via `Kernel.transport_solution` + `C^{p-3k}` collision regularity (`prop:eng-corr1`). |
| `W_osc`, `M_osc` | **(E)** (~50 L) | Immediate from `W_def`, `M_def`, `turn_eq`, `Hz_lb`, `overlap_in_well`, `Y_bound`. |
| `theta_le` | **(E)** (~90 L) | From `M_def`, `rho_one`, `omega_sqrt`, `turn_eq`, `Hz_lb`: `k2 ≥ max(c_H |u_k - u_-|/(4h), (k+1/2)^{1/3})`, so `√h ∑ k2^{-1/2}` is bounded by a Riemann sum for `∫_0^c |u - u_-|^{-1/2} du` (handling `u_- = 0` similarly). |
| `seed_pos` | **(E)** (~30 L) | From `wf_eq`, `pcU_nat` (`PCPhase.lean`), `corr_lead`, `Y_bound`: `φ(0) = (A(h/2) - (h/2) B(h/2) Y(h/2)) κ(-1/2) exp(-Z_0²/4) > 0` for `h` small. |
| `collar_lb` | **(E)** (~60 L) | From `PCEnvelopeAssembled.pc_beyond` + `pc_reflect` at half-integers (for `Z_k < 0`) + `corr_lead` + `turn_eq` + `Hz_lb`: `|h B √h U'| ≤ C h |U|` since `h k2 ≤ C`. |
| `theta_margin` | **(E)** (~60 L) | From `overlap_in_well` + compactness of `P` + joint continuity of `G_0, B_0` (`PrincipalReg` / `CoreReg`): `T(u; X)` attains a strictly positive minimum on `P × [c', c]`, and `E_0` is bounded above. |

### 1.2 `BulkPhaseInputs` (`Charts/BulkWeber.lean`)

| Field | Verdict | Justification / Route / Reuse |
|---|---|---|
| `Sigma` | **(D)** | `Sigma μ 0 X t = actionS0`, `Sigma μ 1 X t = 0`, and `Sigma μ j` (`2 ≤ j ≤ M`) from all-order asymptotic expansion. |
| `Sigma_zero`, `Sigma_one` | **(D)** | Definitional (`Sigma μ 0 := actionS0 (frozenFamily ...)`, `Sigma μ 1 := 0`). |
| `Sigma_reg` (`j = 0`) | **(H)** | `S_0^{(t)}(X) ∈ C^{2M+1}([Jlo, Jhi] × [-t0, t0])` **through collisions** (`lem:smo-S0`). Cheapest route: split `S_0 = Theta_L(u) + Theta_R(L - u)` at fixed `u ∈ [c', c]` using `matchO`; then `Theta_L(u) = ∫_{Y(u)}^{2√u} √(u - t²/4) dt` is `C^{2M+1}` in `Y(u)` (`|Y(u)| < 2√u` strictly) composed with `Y ∈ C^{2M+1}` from WP3b! |
| `Sigma_reg` (`j ≥ 2`), `Sigma_bdd` | **(H)** | For `M ≤ 1`, `j ≥ 2` is vacuous (`Sigma_bdd` for `j = 0` needs uniform `C^{2M+1}` norm of `Y` on `K`). For `M ≥ 2`, requires all-order `C^{2M+1}` expansions of `Sigma_j` (`lem:smo-bulkphase (4)`). |
| `casoratian` (`M ≤ 1`) | **(E)** (~180 L) | Since `max M 1 = 1`, error is `O(h * pre)`! Provable from `PCPhase.pc_phase_osc_lattice` (`O(μ⁻²) = O(h)`), `PCPhase.pcU_eq_hermitePhi` (exact `g(μ_n)` where `kappaBal(-(n+1/2)) √(n!) = 1`!), `BulkPhases.bulk_phase_left`, `BulkPhasesKappa.thetaL_add_mirror` (`Θ_L + Θ_R = S_0`), and `V_0 = √(T / (4u - Y²))` (giving `ρ_L(n) ρ_R(n+1) - ρ_L(n+1) ρ_R(n) = O(h²)`). |
| `casoratian` (`M ≥ 2`) | **(H)** | Requires all-order uniform expansion of `pcU(-(n+1/2), z)` (DLMF 12.10.35 / all-order Hermite Plancherel–Rotach, extending `HermiteBulkMain.lean` beyond `O(n⁻¹)`) and Stirling's asymptotic series for `Gamma`, plus matching with all-order corrector jets. |

### 1.3 `SoftEdgeChart` (`Charts/SoftParabolicCylinder.lean`)

Concrete data: `chainW` is a single-patch turning-point-free Weber ladder on `[0, u_c - η/2]`; `chain` has patch 1 = `chainW` up to `jj 1 = ⌊(u_c - η)/h - 1/2⌋`, and patches 2 & 3 share the PC ladder (`dd = 1`, `d2 = 1`, `ω = √h`, `PiP/PiM` from `T_gen^{PC}` at `a^{[q]}_{PC}` and `zeta`) with switch `jj 2` (`Z_{jj 2} ≤ 0 < Z_{jj 2 + 1}`), `NR = ⌊(u_c + 2η)/h - 1/2⌋`, `jj 3 = NR - 1`.

| Field | Verdict | Justification / Route / Reuse |
|---|---|---|
| `cs, N0, δ0..cT, uc, zeta, muS, Y, chainW, chain` | **(D)** | Data fields. |
| `consts_pos`, `consts_pos2`, `consts_pos3`, `consts_pos4`, `consts_pos5`, `consts_pos6`, `cT_pos` | **(D)** | Positivity of chosen chart constants. |
| `uc_spec`, `ucη_in` (and `FamilyInputs.geom`) | **(E)** (~40 L) | **Already proved** in `TheoremA/GeometrySoft.lean` (`SoftEdge.geomSoft`, `SoftEdge.geomSoftLower` → `GeomSoftConcl`) for `η ≤ η_0`, `δ0 ≤ δ_*`. |
| `zeta_deriv`, `zeta_alpha`, `mu0_zero`, `mu0_deriv`, `mu0_S0`, `mu0_slope`, `muS_bd` | **(H)** | Real two-turning-point Moser coordinate `zeta(x; α)` and quantised shifts `mu_{2r}(α)` (`lem:cha-PCcoord`, `thm:smo-MPS/TPC/WT2`). Cheapest route: construct `zeta(x; 0)` from `tf` (`GeomSoftConcl`), solve `cosh(Ω_0 ∂_x ζ) = Υ_0` via Moser homotopy / Banach fixed point for `α ≠ 0`, and `mu_0` from action equality `π mu_0 = S_0` (`mu0_S0`) + linear extension to `α < 0`. |
| `delta0_small` | **(D)** | Choose `δ0 ≤ cmu0² / (2 cZ² Cmu0)` once `cZ, cmu0, Cmu0` are fixed. |
| `zeta_far`, `zeta_far_out`, `zeta_sign_out`, `zeta_T` | **(E)** (~120 L) | `zeta_far` from `zeta_deriv`, `zeta_alpha`, `mu0_zero`, `mu0_slope`, `delta0_small`; `zeta_sign_out` & `zeta_far_out` from extending `d_x ζ ≥ d_- > 0` across `[-u_c, L - u_c]`; `zeta_T` (~40 L) directly from the defining equation `cosh(Ω_0 ∂_x ζ) = Υ_0` + `T = 4 E_0 (1 - Υ_0²)` + `d_x ζ ≤ d_+`. |
| `Y_forb`, `matchF_soft` | **(H)** | Turning-point-free Weber coordinate `Y_L` on `[0, u_c - η/2]` (`prop:cha-halfrow (b)`, `eq:tha-YLsoft`). Much easier than bulk (`T < 0`, `Q_0 > 0` uniformly by `FamilyInputs.geom`, no collision, no turning point): ~200 L via 1D monotone IFT / `findroot` analysis. |
| `shapeW`, `A_bondW`, `Q_diagW`, `dd_sqrtW`, `omega_sqrtW`, `wfW_eq`, `W_defW`, `M_defW` | **(D)** | Definitional from `chainW` construction (same Weber ladder as `BulkWeberChart`). |
| `validW` (bookkeeping + `ladder` + `env` + `W_mono`) | **(E)** (~200 L) | Reuses `BulkWeberChart` Weber `SymplecticLadder` + `pc_env_well` + `matchF_soft`. |
| `validW` (`cas_lb`, `defect0`, `defect1`, `A_bd`, `B_bd`) | **(H)** | Same localised `Engine/Corrector` + `SymbolExp` pipeline as bulk, **but with NO turning point and NO collision** on `[0, u_c - η/2]` (`prop:eng-corr1` is not needed, only algebraic corrector recursion on `[0, u_c - η/2]` + hard-edge fix). |
| `theta_leW` | **(E)** (~40 L) | Since `Y² - 4u ≥ cF > 0`, `M_k ≤ C h^{1/4}`, so `theta ≤ C ≤ C * Lm(h)` (using `Lm_one`). |
| `seed_posW`, `collar_lbW`, `lb_weber` | **(E)** (~60 L) | Same as `BulkWeberChart.seed_pos`, `collar_lb` (using `pc_beyond` and `corr_lead` on `chainW`). |
| `patch1_eq`, `shape`, `A_bond`, `Q_diag`, `shared_PC`, `d2_PC`, `wf2_eq`, `wf3_eq`, `W1_def`, `M1_def`, `W2_def`, `W3_def`, `M2_def`, `Lm_one`, `Lm_small` | **(D)** | Definitional by construction of `chain` (`Lm = 1` or `1 + log(1/h)`). |
| `switch_in` | **(E)** (~40 L) | From `ucη_in`, `zeta_deriv`, `zeta_far`, `zeta_sign_out` (IVT gives `ζ(·; α) = 0` in `(-η/4, η/4)`). |
| `valid` — bookkeeping + `ladder` (patches 2, 3) | **(E)** (~250 L) | PC `SymplecticLadder` on patches 2 & 3 (`dd = d2 = 1`, `ω = √h`, `PiP/PiM = T_gen^{PC}`): uses `pcExactFacts` (`pc_wronsk`, `pcU_ode`, `pcV_ode`, `pc_reflect_V` for `a = 0` Wronskian), `ODE.exists_linear_system`. `(SM3)` holds because `h * a^{[q]}_{PC} = -muTilde(h)` is even in `h`! |
| `valid.env`, `valid.W_mono` | **(E)** (~150 L) | `env` from `pc_env_well` + `pc_env_bar` + `pc_reflect`/`pc_reflect_V` + `pcSwap_eq_pcMinus` + `WindowEnvelopes.ewell_lower` near `j_2`; `W_mono` from `matchF_soft`, `zeta_deriv`, `ewell_lower` at `j_2`. |
| `valid.cas_lb`, `valid.defect0`, `valid.defect1`, `valid.A_bd`, `valid.B_bd`, `corr_PC` | **(H)** | Localised `Engine/Corrector` + `SymbolExp` + `prop:eng-corr1` on `[u_c - η/2, u_c + 2η]` for the PC ladder (two simple turning points coalescing at `α = 0`, no hard edge!). |
| `theta_le` | **(E)** (~80 L) | From `M2_def`, `zeta_deriv`, `zeta_far`, `muS_bd` (Riemann sum as in bulk; for `q = m - 1`, `ρ_k` weight yields `log(1/h)`). |
| `bondA_le` | **(E)** (~20 L) | Directly from `TheoremA/StepZeroCore.lean` (`bondA_le`) + `(E_K)`. |
| `grow_gap` | **(E)** (~60 L) | From `SoftEdge.UData.gap` (`GeometrySoft.lean`: uniform margin `f_+ + γ ≤ X_s^+` on `|u - u_c| ≥ η/4`) + `StepZeroCore.bondA_le` + `(E_K)` remainder. |
| `ratioM` | **(E)** (~50 L) | Both `k2` values at `j_1, j_1+1` lie in `[c/h, C/h]` by `Y_forb`, `zeta_far`, `zeta_deriv`, `muS_bd`. |
| `lb_pc` | **(E)** (~60 L) | Modulo `corr_PC`: uses `PCEnvelopeAssembled.pc_beyond` directly at `-Z_k > 2√(max(-a,0))` (both `a ≤ 0` and `a > 0`)! |
| `lamL_cont` | **(E)** (~120 L) | From `PCSmoothFacts.cont_U/V`, `PCPositive.cont_pcUD/VD`, `PCExact.pc_reflect_V` at `a = 0`, and `valid.cas_lb` (factoring out `s(a)` that jumps at `a = 0` so `pcMinus 1 / s(a)` is continuous at `a = 0`, and cancelling `s(a)` between numerator and denominator!). |
| `ratio2`, `grow3` | **(E)** (~220 L) | Modulo `corr_PC` (+ `C^1` of `AA_2` in `u`): does **NOT** need near-turning-point `V_growth`! Uses: (i) far-region `V > 0, V' ≥ c √k2 V` proved from `PCEnvWellFar.abs_vt_well_far_le` + `PCEnvCompact` for `a ≤ 0` and `z² - 4A ≥ c/h` (~120 L); (ii) `PCLaplace.pcU_pos_of_gt` + Riccati bound `|U'(a,-z)| ≤ C √k2 U(a,-z)` for `a > 0` (~60 L). |

### 1.4 `SoftPhaseInputs` (`Charts/SoftPhaseInputs.lean`)

| Field | Verdict | Justification / Route / Reuse |
|---|---|---|
| `w, ρ, w_pos, ρ_nonneg, window_in_chart` | **(D)** | Choose `w = C.δ0 / 4`, `ρ = C.δ0 / 16` (`w + ρ ≤ C.δ0`). |
| `bandHi_close` | **(E)** (~60 L) | From `CoreReg.contBandHi` (`StepZeroCore.lean`) on `frozenFamily` + compactness of `K`: shrink `t0` so `|bandHi(μ, t) - bandHi(μ, 0)| ≤ ρ`. |
| `bandHi_reg` | **(H)** | `bandHi(μ, t) = f_+(u_c(μ, t); μ, t)` is `C^{2M+1}` in `t` (`C^{2M+1}` Implicit Function Theorem applied to `∂_u f_+(u; μ, t) = 0` using `f_+'' < 0` from `H3p`; ~200 L). |
| `muS_reg`, `Sigma_bdd` | **(H)** | `mu_{2r}(α, t) ∈ C^{2M+1}` jointly in `(α, t)` (`thm:smo-MPS/TPC/WT2`) + quantitative `C^{2M+1}` chain rule + compactness of `K` for uniform `Sigma_bdd`. |

### 1.5 `TransferInputs`, `TransferInputsDn` (`Charts/TransferCoefficients.lean`), and `TransferBundle` (`TheoremB/Statements.lean`)

| Field | Verdict | Justification / Route / Reuse |
|---|---|---|
| `TransferInputs / TransferInputsDn`: `N0, cT, cα, S, ωmax, κ, consts_pos` | **(D)** | Data + positivity (`κ` = `g_{m/2}` for even `m`, `b_{(m+1)/2}` for odd `m`). |
| `same_ladder` | **(D)** | Construct `CI0` (order `m`) and `CI1` (order `m+1`) from the **same** Weber/PC ladder (`Y, zeta, muS, dd, d2, PiP, PiM, wf, ω` independent of `m`). |
| `parity_A`, `parity_B` | **(D)** (~15 L) | Definitional from `AA = Ahat g m`, `BB = Bans b (m/2)` (`Engine/Corrector.lean`). |
| `reg_t11`, `reg_t12` | **(H)** | Uniform `BoundedC2` of `(PiP 1)_{00/01}` (bulk) and `(PiM 2)_{00/01}` (soft): differentiating the linear ODE `T_gen` twice in `(u, X)` uniformly in `h` from `C^3` bounds of `Y` and `zeta` (`lem:smo-budget (b)-(d)`). |
| `reg_A1`, `reg_B1`, `reg_κ` | **(H)** | Uniform `BoundedC2` of `g_i, b_i` (`prop:eng-corr1`, `lem:smo-budget (e)`). |
| `t12_lb`, `alpha_lb` | **(E)** (~120 L) | Modulo `O(h)` Taylor expansion of `PiP/PiM` around `h = 0` (`reg_t12`) + `corr_lead`/`corr_PC`: at `h = 0`, `|t_{12}| = V_0/P_0 > 0` (bulk) or `|V_0|/P_0 > 0` (soft), and `α = A^{[m+1]} - h B^{[m+1]} t_{11}/t_{12} = g_0 + O(h) ≥ c_α > 0`. |
| `omega_pos_le` | **(E)** (~20 L) | Bulk: `0 < √s_k ≤ √L` on `[0, c + σ/2]`. Soft: `Dm 1 = 1`. |
| `TransferBundle` (`bulkL, bulkR, softUpL, softUpR, softLoL, softLoR`) | — | Six instances of `TransferInputs` / `TransferInputsDn` above (`mirrorFamily` and `negFamily` inherit the same regularity/bounds). |

### 1.6 `ChartInputs` (`Charts/ChartInputs.lean`) and `Layer4Inputs` (`Assembly/ThmAi.lean`)

| Field | Verdict | Justification / Route / Reuse |
|---|---|---|
| `ChartInputs.pc` | **(X)** (current) / **(E)** (refactored) | Currently **(X)** because `PCEnvelopeAssembled.parabolicCylinderFacts_of_vGrowth` still requires the unproved, Airy-hard `PCEnvelopeFacts.V_growth` (`max(2√(max(-a,0)), 1) ≤ z`), which is unconsumed by Layers 2–3. Immediately **(E)** if `V_growth` is dropped or restricted to the far zone. |
| `Jlo, Jhi, nb, lo, hi, bulkL, bulkR, softUpL, softUpR, softLoL, softLoR` | — | Sub-bundles (see §§1.1, 1.3; note `bulkL/R` require localising `K` to `K' ⊆ K` per `F-geom2`). |
| `overlap_match` | **(D)** | Define `(bulkR ν).c := F.L - (bulkL ν).c'`, `(bulkR ν).c' := F.L - (bulkL ν).c`, `(bulkR ν).σ := (bulkL ν).σ`; compatibility with `overlap_in_well` follows from `BulkProof.uMinus_mirror`. |
| `mirror_up`, `mirror_lo` | **(D)** + **(E)** (~80 L) | Define `CR` by `CR.uc = L - CL.uc`, `CR.zeta p α x = -CL.zeta p α (-x)`, `CR.muS = CL.muS`, `CR.η = CL.η`, `CR.δ0 = CL.δ0`, `CR.N0 = max CL.N0 ...` (using the same `N0` for `CL` and `CR`). Verify `CR` coordinate/action identities by `u ↦ L - u`. |
| `cover_bulk`, `blocks_in_J`, `cover` | **(E)** (~120 L) | On localised `K' ⊆ K` and small `t0` (so `osc(bandLo) < δ0_lo/2`, `osc(bandHi) < δ0_up/2` via `CoreReg.contBandLo/Hi`), pick `[Jlo, Jhi]` inside `(bandLo, bandHi)` reaching within `δ0/2` of both ends; cover `[Jlo, Jhi]` by finitely many open balls from `Margins.partA` (`GeometryMargins.lean`) and clamp to `[Jlo, Jhi]`. |
| `Layer4Inputs`: `Kidx, t0, U, V, cPC, CPC, CI, PI, ht0, SIu, SIl` | — | See `ChartInputs`, `BulkPhaseInputs`, `SoftPhaseInputs` above (with `truncSM G M = truncFamily G M`, verified definitionally). |
| `Layer4Inputs`: `hw, hlt, hJhi, hJlo, hwb, hKidx` | **(E)** (~40 L) | Set `Kidx := (M + 1)/2`, `w := min SIu.w SIl.w` (shrunk so `w ≤ bandHi - bandLo`), `Jlo < bandLo + w`, `bandHi - w < Jhi`, `lo ν < hi ν`. |

---

## 2. Independent Work Packages (Task 1)

Ordered by dependency (recommended execution order: **WP0 → {WP1a, WP1b, WP2} → {WP3a, WP3b, WP4} → WP5 → WP6**).

### WP0: Structural Unblockers (Prerequisite cleanup)
* **WP0a (Unblock `ChartInputs.pc`)**: Drop unconsumed `V_growth` from `PCEnvelopeFacts` (or restrict it to `z ≥ max (z2Airy a) 1` for `a ≤ -4`, `z ≥ 1` for `a > -4` and prove it from `PCEnvWellFar` + `PCEnvBar` + `PCEnvCompact`). Reuses: `PCEnvelopeAssembled.lean`, `PCEnvWellFar.lean`, `PCEnvBar.lean`.
* **WP0b (Unblock `Engine/Corrector` at hard edge `s = 0`)**: Replace `CorrSetting.nondeg` with `adj_Pi : ∀ u h, PiP u h = adj (PiM (u + h) h)` (and localise `UO`/`PApprox` to compact `[a, b]`). Reuses: `Engine/Defect.lean` (`Pp_entries_of_prod`, `green_identity`, `Fcas_even`), `Engine/CorrectorDefect.lean`, `Engine/Corrector.lean`.
* **First lemma (WP0a, far-zone `V_growth`)**:
  ```lean
  theorem pcV_growth_far : ∃ cV : ℝ, 0 < cV ∧ ∀ a z : ℝ,
      (a ≤ -4 → z2Airy a ≤ z) → (-4 < a → 1 ≤ z) →
      2 * Real.sqrt (max (-a) 0) + 1 ≤ z →
      0 < pcV a z ∧ cV * Real.sqrt (k2 a z) * pcV a z ≤ deriv (pcV a) z
  ```

### WP1: Exact Symplectic Ladders & Envelope/Weight Discharge `(E)`
Can be split into two parallel sub-packages (**WP1a** and **WP1b**) with zero `(H)` dependencies:
* **WP1a (Exact Weber & PC `SymplecticLadder` + `env` + `lamL_cont`, ~750 L)**:
  * Builds concrete `weberLadder` (`PiP, PiM` via `ODE.exists_linear_system`) and `pcLadder`, proves `SymplecticLadder` + `annih`, `valid*.env`, and `SoftEdgeChart.lamL_cont`.
  * Reuses: `PCExact.pcExactFacts`, `PCSmooth.pcSmoothFacts`, `PCPositive.cont_pcUD/VD`, `PCEnvelopeAssembled.pc_env_well`, `pc_env_bar`, `ODE.exists_linear_system`.
  * **First lemma**:
    ```lean
    theorem weber_symplecticLadder (Y : ℝ → ℝ) (hY : ContDiff ℝ 2 Y) :
        ∃ PiP PiM : ℝ → ℝ → M2,
          SymplecticLadder (1 / 2) (fun s _ => Real.sqrt s) (fun s _ => s)
            (fun _ _ => 1) (fun _ _ => 0) PiP PiM (weberWf Y pcU pcV) (fun h => Real.sqrt h)
    ```
* **WP1b (Far-region `V` growth, `ratio2`, `grow3`, `ratioM`, `bondA_le`, `grow_gap`, ~400 L)**:
  * Proves far-region `V > 0`, `V' ≥ c_V √k2 V` from `PCEnvWellFar.abs_vt_well_far_le` + `ut_vt_wronsk`, plus Riccati bound for `U'(a, -z)/U(a, -z)` (`a > 0`), and discharges `bondA_le`, `grow_gap`, `ratioM`, and (modulo `corr_PC`) `ratio2`, `grow3`, `lb_pc`.
  * Reuses: `PCEnvWellFar.env_well_far_U_V`, `PCLaplace.pcU_pos_of_gt`, `PCBeyond.pcU_beyond_riccati_le`, `StepZeroCore.bondA_le`, `GeometrySoft.UData.gap`.
  * **First lemma**:
    ```lean
    theorem pcV_far_pos_growth : ∃ cV K0 : ℝ, 0 < cV ∧ 0 < K0 ∧ ∀ a z : ℝ, a ≤ 0 →
        z2Airy a ≤ z → K0 ≤ ∫ t in (2 * Real.sqrt (-a))..z, Real.sqrt (t ^ 2 / 4 + a) →
        0 < pcV a z ∧ cV * Real.sqrt (k2 a z) * pcV a z ≤ deriv (pcV a) z
    ```

### WP2: Localised Geometry, Cover & Mirror Symmetry `(E)` (parallel to WP1)
* Discharges `BulkWeberChart.overlap_in_well`, `theta_margin`, `SoftEdgeChart.uc_spec`, `ucη_in`, `switch_in`, `SoftPhaseInputs.bandHi_close`, `ChartInputs.overlap_match`, `mirror_up`, `mirror_lo`, `cover_bulk`, `blocks_in_J`, `cover`, and `Layer4Inputs` cover relations (`hw..hKidx`) on a localised parameter neighbourhood `K' ⊆ K`.
* Reuses: `Margins.geomMargins`, `HypMorse.geomBulk`, `SoftEdge.geomSoft`, `SoftEdge.geomSoftLower`, `CoreReg.contBandHi/Lo`, `BandFacts.bandLo_lt_bandHi`, `BulkProof.uMinus_mirror`, `WindowCoverProof.windowCover_of_charts`.
* **First lemma**:
  ```lean
  theorem local_cover_of_geom {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par)
      {K : Set Par} (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 1) (μ0 : Par) (hμ0 : μ0 ∈ K)
      {δup δlo : ℝ} (hδup : 0 < δup) (hδlo : 0 < δlo) :
      ∃ K' ∈ 𝓝[K] μ0, ∃ t0 Jlo Jhi : ℝ, 0 < t0 ∧
        ∀ p ∈ paramSet K' t0, (frozenFamily F 0).bandLo p < Jlo ∧ Jlo ≤ Jhi ∧
          Jhi < (frozenFamily F 0).bandHi p ∧
          (frozenFamily F 0).bandHi p < Jhi + δup ∧ Jlo - δlo < (frozenFamily F 0).bandLo p
  ```

### WP3: Weber–Langer Coordinate `Y` `(H)` (independent of WP1/WP2)
* **WP3a (Soft Weber coordinate `Y_L` on `[0, u_c - η/2]`, ~250 L)**: Construct `Y_L` solving `matchF_soft`, prove `Y_forb` and `C^{r-2}` regularity in `(u, X)`. (No turning point, no collision!)
* **WP3b (Bulk Weber coordinate `Y` through collision `X = B_0(0)`, ~700–1000 L)**: Construct `Y(u; X)` solving `matchF`/`matchO`, prove `turn_eq`, `Hz_lb`, and `C^{r-2}` (`BoundedC2`) jointly in `(u, X)` across `u = u_-` and `X = B_0(0)`.
* Reuses: `GeometryCollision.geomCollision`, `GeometryBulk.geomBulk`, `GeometrySoft.geomSoft`, `BulkPhasesPC.integral_sqrt_sub_sq`.
* **First lemma (WP3a)**:
  ```lean
  theorem exists_soft_weber_coord {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par)
      {K : Set Par} (hK : IsCompact K) (hH : HypOn F K) (hR : PrincipalReg F K 5)
      {η δ0 : ℝ} (uc : Par → ℝ) (hgeom : ...) :
      ∃ (Y : Par → ℝ → ℝ → ℝ) (Fstar cF S : ℝ), 0 < Fstar ∧ 0 < cF ∧
        (∀ μ ∈ K, BoundedC2 (fun u X => Y μ X u) 0 (uc μ - η / 2) (F.bandHi μ - δ0) (F.bandHi μ + δ0) S) ∧ ...
  ```

### WP4: Soft-Edge Moser Coordinate `zeta`, Shifts `mu_{2r}` & `SoftPhaseInputs` `(H)` (depends on WP2/GeomSoft)
* Construct `zeta(x; α)` and `mu_{2r}(α)` (`lem:cha-PCcoord`, `thm:smo-MPS`, `thm:smo-TPC`, `thm:smo-WT2`), prove `zeta_deriv`, `zeta_alpha`, `mu0_*`, `muS_bd`, `zeta_T`, `muS_reg`, plus `bandHi_reg` (`C^{2M+1}` IFT) and `Sigma_bdd`.
* Reuses: `SoftEdge.geomSoft` (`tf` Morse coordinate, `GeomSoftConcl`), `ActionDerivativeDt`.
* **First lemma**:
  ```lean
  theorem exists_moser_pc_coord {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par)
      {K : Set Par} (hK : IsCompact K) (hH : HypOn F K) (hR : PrincipalReg F K r) (hr : 5 ≤ r) :
      ∃ (uc : Par → ℝ) (zeta : Par → ℝ → ℝ → ℝ) (mu0 : Par → ℝ → ℝ) (η δ0 dm dp cZ cmu0 Cmu0 : ℝ), ...
  ```

### WP5: Localised Correctors, `SymbolExp`, and `TransferInputs` Regularity `(H)` (depends on WP0b, WP1a, WP3, WP4)
* Derive `SymbolExp` on compact intervals `[0, c+σ]` / `[u_c - η/2, u_c + 2η]` from `EK` + `C^3` of `Y`/`zeta`; prove `prop:eng-corr1` (`C^{p-3k}` regularity of `b_k, g_k` uniformly in `(μ, t, X)` through turning points/collisions); discharge `cas_lb`, `defect0/1`, `A_bd`, `B_bd`, `corr_lead`, `corr_PC`, `seed_pos`, `collar_lb`, `lb_weber`, and `TransferInputs`/`TransferInputsDn` (`reg_*`, `t12_lb`, `alpha_lb`).
* Reuses: `Engine/Corrector.lean`, `Engine/Kernel.lean` (`transport_solution`), `BulkPhases.lean`, `SoftTransfer.lean`.
* **First lemma**:
  ```lean
  theorem localized_eng_corr_full (a b : ℝ) (hab : a < b) (K : ℕ) ... :
      UO (2 * K + 2) (fun u h => ...) -- on u ∈ [a, b] with adj_Pi replacing nondeg
  ```

### WP6: Bulk Phase Inputs `(E)`/`(H)` (depends on WP1a, WP3b, WP5)
* **WP6a (`M ≤ 1`, enough for `CorEigen`, ~250 L)**: Prove `lem:smo-S0` (`S_0^{(t)} ∈ C^{2M+1}` through collisions from `matchO` + WP3b `Y` regularity) and `BulkPhaseInputs.casoratian` (`O(h)` error) from `PCPhase.pc_phase_osc_lattice` + `BulkPhases.bulk_phase_left` + `BulkPhasesKappa.thetaL_add_mirror`.
* **WP6b (`M ≥ 2`, full `ThmAi`/`ThmSmoSpec`, `(H)`)**: Prove all-order uniform asymptotics of `pcU(-(n+1/2), z)` (extending `HermiteBulkMain.hermite_bulk_PR` to `O(n^{-M})`) + Stirling series for `Gamma` + matching to get `Sigma_2..Sigma_M` and `O(h^M)` in `casoratian`.
* **First lemma (WP6a)**:
  ```lean
  theorem actionS0_smooth_through_collision {Par : Type*} [TopologicalSpace Par]
      (F : SymbolFamily (Par × ℝ)) (K : Set Par) (t0 Jlo Jhi : ℝ) (M : ℕ)
      (CL : BulkWeberChart F (paramSet K t0) Jlo Jhi (max M 1) pcU pcV)
      (hYreg : ∀ μ ∈ K, ContDiffOn ℝ (2 * M + 2) (fun p : ℝ × ℝ × ℝ => CL.Y (μ, p.2.2) p.2.1 p.1) ...) :
      ∀ μ ∈ K, JetRegJ (fun X t => actionS0 F (μ, t) X) (Set.Icc Jlo Jhi) t0 (2 * M + 1)
  ```

---

## 3. Concrete `BulkWeberChart`, False/Unsatisfiable Fields & Numerical Checks (Task 2)

1. **Can a concrete instance of `BulkWeberChart` be built now?**
   * **No, not from currently proved lemmas alone.** The exact Weber `SymplecticLadder` (`dd = √s`, `d2 = s`, `PiP/PiM` via `ODE.exists_linear_system`), `annih`, `valid.env`, `valid.W_mono`, `W_osc`, `M_osc`, `theta_le`, `overlap_in_well` (for localised `K'`), `theta_margin`, `seed_pos` (mod `corr_lead`), and `collar_lb` (mod `corr_lead`) **can all be built now** (~870 L total).
   * However, **two `(H)` components remain unproved**: (i) the matched Weber–Langer coordinate `Y` (`turn_eq`, `Hz_lb`, `matchF`, `matchO`, `Y_bound`, especially `C^2` through the collision `X = B_0(0)`), and (ii) the localised hard-edge correctors & `SymbolExp` (`valid.cas_lb`, `valid.defect0`, `valid.defect1`, `valid.A_bd`, `valid.B_bd`, `corr_lead`), which are also currently blocked `(X)` by `CorrSetting.nondeg` failing at `s = 0` (`d2 0 h = 0`).

2. **Fields that look false, unsatisfiable, or subtly constrained (verified by source inspection + `mpmath`):**
   * **`ChartInputs.pc` (currently blocked `(X)` by `PCEnvelopeFacts.V_growth`)**: `PCEnvelopeAssembled.parabolicCylinderFacts_of_vGrowth` leaves `V_growth` (`max(2√(max(-a,0)), 1) ≤ z`) as an open hypothesis because near `z = 2√(-a)` for `a ≤ -4` it is Airy-hard (`E6` in `LAYER4_PCF_PLAN.md`), even though **no proof in Layers 2–3 consumes `V_growth`**, and `SoftEdgeChart.ratio2`/`grow3` only need `V_growth` in the far exponential zone `z² - 4A ≥ c/h`.
   * **`BulkWeberChart.overlap_in_well` on global compact `K` (`F-geom2`)**: Unsatisfiable for a single `(lo ν, hi ν, c' ν, c ν)` across an unlocalised compact `K` if `u_c^+(μ₁) < u_c^-(μ₂)`. Satisfiable once `K` is localised to compact neighbourhoods `K' ⊆ K` (`Margins.geomMargins`).
   * **`BulkWeberChart.overlap_in_well` right endpoint `c ≤ u_+ - σ` vs `Y_bound` on `[0, c + σ]`**: Allowing `c = u_+ - σ` puts `c + σ = u_+` at the right turning point (where `thetaL` has a `√(u_+ - u)` singularity). When building a concrete chart from `Margins.geomMargins` (`c ≤ u_+ - δ₁`), one must pick `σ ≤ δ₁ / 2` so `c + σ < u_+` strictly.
   * **Signs & identities verified sound (mpmath 1.3.0, 30–40 digits):**
     * `agy_scratch/check_weber_ladder.py`: verified `(SM1)-(SM3)`, `det Π₊ = u + h/2`, `det Π₋ = u - h/2`, `Π₋(u+h, h) Π₊(u, h) = (u + h/2) I`, `Π₊(u, -h) = Σ Π₋(u, h) Σ`, and `shift_up`/`shift_dn` for both `pcU` and `pcV` at `j = 0, 1, 2` to **`~1e-41`**.
     * `agy_scratch/check_t12_bulk.py`: verified `Y > 0` (`X > B_0(0)`), `Y < 0` (`X < B_0(0)`), `t_{12}(u, 0) = Π₊(u, 0)_{01} < 0` (`V_0 = -P_0 t_{12} > 0`, `g_0 = V_0^{-1/2} > 0`), and `P_0 (Π₊(u,0)_{00} + Π₋(u,0)_{00}) = Q_0(u)` (`eq:eng-langer`) analytically and numerically for both `X > B_0(0)` and `X < B_0(0)`.
     * Verified `BulkWeberChart.wf_eq` + `W_def` + `Valid.env` for `X < B_0(0)` (`Z_k < 0`): valid because `a_k = -(k + 1/2)` is a half-integer (`cos(π a_k) = 0`), so `|U(a_k, -z)| = |U(a_k, z)|` and `|V(a_k, -z)| = |V(a_k, z)|`.
     * Verified `SoftEdgeChart.lamL_cont` across `a = 0`: `kappaBal(a)` jumps by `(π/2)^{1/4}` (checked from the definition: `π^{-1/4}` from the left, `2^{-1/4}` from the right) and `pcMinus 1` jumps by the matching factor (`V(0, -z) = π^{-1/2} U(0, z)`), but the jump cancels identically between the numerator and denominator Casoratians of `lamL`.

---

## 4. Recommended Restructurings (Task 3)

1. **Drop `V_growth` (or restrict to the far zone) in `PCEnvelopeFacts` (`Charts/ParabolicCylinder.lean`)**: Removes the sole remaining hypothesis of `PCEnvelopeAssembled.parabolicCylinderFacts_of_vGrowth`, immediately making `ChartInputs.pc` proved `(E)` for `pcU, pcV`. (Unconsumed fields `ode_V`, `shift_*` are already proved in `PCExact.lean`.)
2. **Replace `CorrSetting.nondeg` with `adj_Pi : ∀ u h, PiP u h = adj (PiM (u+h) h)` and localise `Engine/Corrector.lean` to `[a, b]`**: `Engine/Corrector*.lean` only uses `nondeg` via `Pp_entries_of_prod`; `adj_Pi` holds identically on the Weber ladder even at `s = 0` (`u = -h/2`).
3. **Shrink `BulkWeberChart` and `SoftEdgeChart` by deriving redundant fields as lemmas**:
   * In `BulkWeberChart`: `W_osc`, `M_osc` follow from `W_def, M_def, turn_eq, Hz_lb, overlap_in_well, Y_bound`; `seed_pos`, `collar_lb` follow from `wf_eq, corr_lead, Y_bound, beyond`; `theta_le` follows from `M_def, turn_eq, Hz_lb, rho_one, omega_sqrt`.
   * In `SoftEdgeChart`: `uc_spec, ucη_in, grow_gap` follow from `GeomSoftConcl` + `EK`; `bondA_le` follows from `EK` (`StepZeroCore.bondA_le`); `delta0_small, zeta_far` follow from `zeta_deriv, zeta_alpha, mu0_*`; `seed_posW, collar_lbW, lb_weber, lb_pc, lamL_cont, ratioM, ratio2, grow3` follow from `corr_lead`/`corr_PC` + `PCEnvelopeFacts` + far-region `V_growth`.
4. **Add `Y, c, c', σ` matching to `ChartPair` (`TheoremB/Statements.lean`)**: `ChartPair` already equates soft data (`soft_up_eq`, `soft_lo_eq`); equating bulk `Y, c, c', σ` between `CI0` and `CI1` makes `TransferBundle.same_ladder` automatic.
5. **Localised gluing wrapper for `Layer4Inputs` / `ChartInputs`**: done for `ThmAi`, `ThmAii`, `ThmB` (`Assembly/CoverGlue.lean`); `Layer4Inputs`-level gluing (the windows of `thmAi_assembled`) is not needed for `ThmAi`, which glues from its pieces (`thmAi_of_cover`).
6. **Expose `M ≤ 1` `BulkPhaseInputs`**: Split out the `M ≤ 1` case (`CorEigen` only uses `M = 0, 1`), which needs only `PCPhaseFact.phase_osc` (`O(h)`) and `lem:smo-S0`, avoiding all-order DLMF 12.10.35 / Stirling.

---

## 5. Paper Findings & Improvements (Task 4)

Already documented in `PLAN.md` / `GeometryStatements.lean` / `LAYER4_PCF_PLAN.md` (verified against the Lean freeze):
* **`F-SM1` (`app_thmA.tex`, `lem:smo-SM`)**: needs `G_j` bounded on `[0, L]` for `j ≤ M`.
* **`F-geom` & `F-geom2` (`thmA.tex`, `lem:tha-geom (c)`, `sec:tha-standing`)**: single overlap `(c', c)` fails globally in `X` when `u_c^+ < u_c^-` and globally in `μ` on unlocalised `K`; holds per energy block and per parameter neighbourhood `N ∈ 𝓝[K] μ₀`.
* **`F-A7` (`app_thmA.tex`, `lem:tha-count`)**: needs `N ≥ 1`, `a_n > 0` (`0 ≤ n < N`), `I` an interval.
* **`F-W2-9` (`thmA.tex`, `prop:tha-W2 (1)`)**: PC range should be strict `u_c - η/2 < u_n` (avoiding overlap with Weber range at one row).
* **`F-W2-11` (`app_thmA.tex`, Step 3)**: uses `|μ_{2r}(X)| ≤ C_μ` (`a ≤ a_+`) implicitly.
* **`F-t0` (`thmA.tex`, `thm:A(ii)`, `thm:B`)**: requires `0 < h ≤ min(h_m, t_0)`.
* **`F-E1` (`app_thmA.tex`, Step 0)**: `O(h²)` holds relative to the *frozen* band `X_s^±(h)` (`O(h)` for the unfrozen band).
* **`F-BB-1` & `F-E2..E4` (`main_results.tex`, `cor:eigen`)**: requires `δ > 0`, `δ' ≤ δ`, `X_k` in the Lipschitz neighbourhood, and only `x_0` in (c).
* **`F-loc` (`thmA.tex`, `sec:tha-standing`)**: uniform margins require `IsCompact K` and joint continuity of jets (`JetReg`).
* **`F-CC1` (`app_thmB.tex`, `prop:thb-inputs`)**: right soft chart must start at `g₀ = N - nearestRow(L - u_c)` (not `n_c + 1`) when `u_c/h ∈ ℤ`.
* **`F-DD1` (`thmB.tex`, `cor:thb-Dm`)**: `ThmB` for `truncFamily F m` uses only `(D_1)` and `(E_{Kidx})` (`StdDM`), not `(D_{2 Kidx + 1})`.
* **`F-PC1`, `F-PC2`, `F-PC3`**: `V_growth` is false at `z = 0` (`V'(1/2, 0) = 0`, `V(3/2, 0) = 0`); `phase_osc` is only needed on `μ² = 2n + 1`; joint `ContDiff` of `U, V` is unused (slice `ContDiff` + joint continuity suffices).

**New findings from this Layer-4 audit:**
1. **`thm:eng-corr` (`engine.tex` / `app_engine.tex`)**: states `𝒟² ≠ 0` as bond nondegeneracy, which excludes the Weber hard-edge bond `s = 0` (`𝒟²(0, h) = 0`). The actual algebraic requirement is `Π₊(u, h) = adj Π₋(u + h, h)`, which holds through `s = 0` by continuity (`S₊ = adj S₋` and `det T = 1`).
2. **`lem:tha-geom (c)` / `prop:cha-halfrow (a)` (`thmA.tex` / `charts.tex`)**: `c ≤ u_+ - σ` allows `c + σ = u_+` (touching the turning point where `Θ_L` has a square-root kink), whereas `lem:smo-budget (b)` requires `Y ∈ C^{r-2}` on `[0, c + σ]`. Tightening `c ≤ u_+ - 2σ` keeps `[0, c + σ]` strictly inside the well.
3. **`prop:tha-W2` / `lem:cha-PCenv` (`app_thmA.tex` Step 3 (ii), Step 5)**: near-turning-point `V_growth` (`2√(-a) ≤ z ≤ z₂(a)`) is never used; `V > 0` and `V'/V ≥ c √k₂` are only needed in the far exponential zone `z² - 4A ≥ c/h`.
4. **`app_thmA.tex` Step 6 (`lamL_cont`)**: `κ_bal(a)` jumps by `(π/2)^{1/4}` at `a = 0` (corrected from the report's `2^{1/4}`) and the second pair member `pcMinus 1` jumps correspondingly (since `V(0, -z) = π^{-1/2} U(0, z)`); continuity of `λ_L(X)` across `a = 0` holds because this scalar discontinuity cancels between the numerator and denominator Casoratians.
