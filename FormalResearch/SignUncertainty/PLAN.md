# Paper I (Fourier sign uncertainty, Cohn–Elkies) — Lean plan

Source: QIprojects `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex` (+ supplement, `CFT/common/`).
Supersedes the "Wave 10–12" plan left after Wave 9 (`7ae7af6`). Audit date 2026-11-23, reasoner `778feac`.

## 1. Where we are

- 64 files, about 64k lines (CohnElkies about 40k, SignUncertainty 14k, TwoEdgeBootstrap 4k, Asymptotics 3k).
  `lake build FormalResearch.SignUncertainty FormalResearch.TwoEdgeBootstrap` passes (9269 jobs, about 9 min). There are no
  placeholder proofs or custom axioms, and the headline theorems use only the standard three axioms.
- **No headline result of Paper I is Lean-checked, not even conditionally on a TeX theorem.** The four introduction
  theorems are `thm:intro-radii` (sign-uncertainty radii plus `gt:7.12` CE radius), `thm:intro-separation` (`gt:7.9c`),
  `thm:intro-hb` (`thm:hb-thresholds`) and `thm:intro-gap` (`thm:ce-shell-gap`).
  - The Hankel problem now has its concrete kernel: `hankelKernelData (hc : 1/2 < c)` is unconditional (`HankelBessel*`,
    real-order Bessel in `Special/Bessel*`), and the `±1` Laguerre modes of `gt:7.9b` are proved eigenfunctions
    (`HankelBesselLaguerre`).
  - `CohnElkiesRadius.ce_radius_airy_order_of_bounds` is only the gluing step. Its hypotheses `hlo` and `hhi` *are* the
    two halves of the theorem, and the module imports none of the Airy or Mellin machinery.
- **Waves 4–9 (about 25k lines) feed only leaves.** About 30 hypothesis packages (`MacroscopicTransferPackage`,
  `GT4CoverageBands`, `PE3OriginData`, `PreEdgeGeneralData`, `AiryTailSymbolSeed`, `MovingDiagFarTail`, …) have only toy non-vacuity witnesses (all functions 0, constants 1, or degenerate parameters), and none has a real
  instance. `MovingDiagFarTail` has no instance at all. Theorems such as GT.2b, GT.3b, GT.4, PE.3 and `cepe:general` are
  stated for an abstract `fhat` that carries the paper's estimates as hypotheses. Nothing builds `W_S`, `W_D` from `Ai`,
  or `h_mellin` from a CE pair.
- Open skeleton fields in `Headlines.lean` (6): `hb_thresholds_lower`, `hb_thresholds_upper`, `shell_reduction_m1`,
  `ce_hb_lift_m1`, `shell_reduction`, `ce_hb_lift`. The Hankel form `HankelShellGapLimit` of `thm:ce-shell-gap` is the
  theorem `hankelShellGapLimit_proved`, and the Euclidean statement follows by `shellGapLimit_of_hankel`. `radial_compactness`, `one_profile_envelope` and the
  Euclidean-to-Hankel dictionary `hankel_euclid_dictionary` (`gt:7.9`) are theorems and no longer inputs.
- `thm:ce-shell-gap` route (`ShellGapHankel.lean`, `ShellGapMassRatio.lean`, `ShellGapWeight.lean`, `ShellGapLaplace.lean`,
  `ShellGapMellin.lean`, `ShellGapTransport.lean`, `ShellGapExtract.lean`): the extraction and constraint system
  `eq:ce-laplace-constraint` is proved (`hankelShellGapLimit_proved`): mass ratio, common-subsequence extraction,
  signs, mass transport, and the Laplace limit with the Mellin reflection. Not part of it and still open: the origin
  floor `liminf h_c(0)/M[f_c] ≥ sup_y L_y(2Q∞)` and `u_* ≤ t_m` (`thm:ce-shell-reduction`, `prop:ce-one-profile`).
- What is genuinely closed and reusable:
  - the Airy base: Theorems D, Q and B with its equality case, Clark two-node, Hermite–Biehler quadrature and
    `at47_*`, and Airy PWS (a)⇔(b);
  - E.1–E.3a (finite dimensions);
  - H.14a and H.14b;
  - `lem:radial-compactness` (`radial_compactness`: Mellin inversion, deep lobe, Montel, Airy-class limit, Fatou) and
    the radial rigidity proof `gt:7.5` from it;
  - the strip Poisson kernel TE.1/TE.1a, the algebra of Bootstrap Stage B, Binet and T.1–T.4;
  - GT.1/GT.1s, O.0–O.2, O.3(1), U.4a, O.11h/j/p/x/n and the pieces of CR.1–CR.4.

## 2. What was wrong with Waves 10–12

1. **Bottom-up with no consumer.** Each wave proves a lemma family under packaged hypotheses, and nothing checks
   that the package is the one a headline needs. The result is many conditional statements and zero headlines.
2. **The plan targets both CE upper routes.** `ce_radius.tex` proves the upper half of `gt:7.12` by
   `thm:ce-hb-lift` with `m₀ = 1` (Route II). Wave 10 also targeted the coherent-square lift `thm:ce-lift` (Route I):
   the GT.4 coverage bands, PF.2, PF.5 and `prop:ce-pre-edge`. Route II needs none of these (checked in the TeX:
   `ce_hb_lift.tex` cites O.11w, CR.4, `lem:hb-seed-mass`, U.2, GT.2b, O.11ak, O.6, `thm:ce-post-edge`, `cepe:general`,
   O.11x, O.11n and `cel:L2a`; post-edge uses GT.2a and GT.3a/b, and GT.3b uses PF.T, PF2L.2, PF.4 and FG.3a).
3. **The base shared by every headline is missing from the plan.** The plan never mentions:
   - the concrete Hankel/Bessel kernel of real order;
   - `gt:7.4` (Mellin strip and majorant);
   - `lem:radial-compactness`;
   - the Langer chart `gt:7.7b/c/p`;
   - the Euclidean ↔ Hankel dictionary (radial Fourier on `Euc d`, including odd `d`; `O(d)` averaging;
     Bourgain–Clozel–Kahane / Cohn–Gonçalves reduction).
4. Wave 12 puts general de Branges (SE.1–SE.5) and `PW·PW` on the path. No headline needs them.

## 3. Strategy

- **Skeleton first (M0).** State each headline in Lean with the paper's constants, on concrete objects:
  - `optimalL1CERadius` (exists);
  - Euclidean `A_sign^±(d)` and its identification with the Hankel thresholds (`hankel_euclid_dictionary`: the radial
    Fourier transform on `ℝ^d` is the Hankel transform for every integer `d ≥ 2`, radial averaging, compact-support
    uncertainty);
  - Hankel thresholds `T^±_{m,c}` with the real Bessel kernel.

  Prove each headline from one input structure whose fields are, one-to-one, the TeX theorems it cites (for
  example `hb_thresholds_lower`, `ce_hb_lift_m1`, `shell_reduction_m1`). Progress is the
  number of skeleton fields still open. A field is closed only when it is discharged by a theorem about the concrete
  objects.
- **Every new module must close or shrink a skeleton field.** Existing packages are either wired into a field's
  proof (instantiated with the real Airy cardinal kernel and real CE data) or deleted (git keeps them). Toy
  witnesses do not count as progress.
- **Cheapest unconditional headlines first, then by sharing.** The strict gap and the separation need only the Hankel
  layer and the one-level upper bound, so they come before the Langer/bootstrap lower half. `thm:intro-radii` at one
  level (`gt:7.9` + `gt:7.12`) is the main target and reuses all of it.

## 4. TeX changes made first (QIprojects branch `papers/p1-route-cleanup`)

- **T1 done (owner decision).** The coherent-square lift (`thm:ce-lift`, GT.0, GT.2, GT.4 + tip profile, `prop:ce-pre-edge`,
  O.11y, PF.2, PF.5, O.11aw, coherent amplitudes) is now the supplement part `ce_coherent_square_lift.tex`, outside Lean scope.
  The paper's transfer appendix keeps what the hb-lift uses, stated for a general seed: the fixed-window formula, absolute
  reflected integration, GT.2b, GT.3a/b and post-edge. Its source is the new Lemma O.11s (`ce_o1_route.tex`: `S_c = θ S_h + γ ε S_0`,
  mass and local/far asymptotics, from O.11w). In Lean, `MacroscopicTransferPackage` needs only the fields GT.3b uses;
  `GT4CoverageBands` and the PF.2/PF.5 consumers are out of scope.
- **T2 verified.** At `m₀ = 1`, `H_N = g₁` and the seed is `F_δ = −f₁ − γ₁δ g₁ + γ₂δ(g₁ + g₁' − f₁) + r_δ g₁`, a combination of three
  Airy squares (now stated in `ce_radius.tex`). U.2, GT.1 and T.6 are needed only for `f₁`, `g₁`, `g₁'` and the source.
- **T3: no change needed.** The internal proof header of `gt:7.9c` lists only what the proof uses.
- **T4 done.** Lemma 7.7c cites `gt:7.4(2)`, which holds for either sign; the circular-looking citation of `thm:hb-thresholds`
  is gone.
- **T5 is Lean-only.** The TeX treats odd `d` as half-integer `c` in the Hankel problem. Lean still needs radial Fourier in odd `d`.
- **Also changed:**
  - The intro now states the prescribed-shell results as a dichotomy (`thm:intro-gap` (i)–(iii)): the O(1) lower bound,
    the strict gap if `L_y(−G_N) < 0` for some `y`, and O(1) attainment for odd `m` with strict Laplace positivity. This is
    the natural M0 skeleton statement for Headline D, with `m = 1` being the CE radius.
  - App F (general de Branges) and E.2–E.3a moved to the supplement. They are not in Lean scope.

- **T6: shorter routes after an external review (agy, checked by independent referees).**
  - `gt:7.9c` no longer uses Langer transport or `thm:hb-thresholds`: `lem:radial-compactness` now converges with first
    derivatives, and the upper half is the one-level O.9′.
  - The hb-lift source is a left-shifted convolution of `g₁` (merged, QIprojects `4d1eeda37`); the Dirichlet diagonal,
    CR.1–4, PF.2L, PF.T and W.0–W.6 move to the supplement with Route I.
  - U.3(3)/O.3(2) by real-line integration by parts and Fresnel; O.4(2) by a Banach contraction with a certified bound
    (merged).
  - H.14a now also gives Laplace-positive odd families, so `thm:intro-gap` (iii) occurs at every odd `m`; intro (ii)
    states the bound `−u_LP/β₁`.

## 5. Milestones (S < 500 lines, M 500–2000, L > 2000; calibration: the Virasoro lower half took about 29k lines)

The order puts the cheapest unconditional headlines first. The strict gap (M3 below) and the separation (Headline S) need only
the Hankel layer, the one-level upper bound and pieces that already exist; the heavy analysis (O-chain, Langer,
bootstrap) comes after them.

**M0 Skeleton (S–M).**
- Concrete definitions and the four headline statements, each proved from its input structure.
- Fix two semantic gaps in existing packages: `SignSeparation.lean` defines `A_sign(d)` as `√(2 T_{d/2})` (the Hankel
  threshold), not the Euclidean infimum; `ShellGapPackage` enforces exact zero-offset shells and quantifies over one
  package, not the infimal `R_d^{CE}` with `o(c^{1/3})` offsets.
- `LangerSignSeparationPackage.langer_approx` is no longer needed (TeX `gt:7.9c` no longer uses Langer); replace it by
  the `C¹` compactness field.
- Delete or archive the dead packages: `GT4CoverageBands`, the PF.2/PF.5 consumers, `MovingDiagFarTail`, the CR.4 and
  PF.2L packages once the convolution source lands.
- Rename overclaiming names (`theorem_H14_strict_gap` → `…_core`; `teb_mellin_o1_lower` docstring).

**M1 Classical leaves (parallel; independent of everything else).**
- Bessel `J_ν` for real `ν`: bounds and Weber integral DLMF 10.22.43; Laguerre modes `(4πΔ/c−1)e^{−2πΔ}` (eigenvalue
  −1) and `e^{−2πΔ}` (+1) (M–L).
- Radial Fourier transform on `Euc d`: even `d` exists (`ModularBootstrap/.../HankelFormula.lean`,
  `fourier_radialLift_apply_eq`); close even-`d` headlines first and do odd `d` in parallel (M). `O(d)` averaging.
- `hNicholson` and `hBesselRatio` are dropped: they served only the Dirichlet-diagonal source (CR.4, W.0–W.6), which
  the convolution source replaces.

**M2 Hankel layer (used by every headline; L).**
- Concrete `HankelKernelData` from M1; `gt:7.4` (strip reflection, majorant, three lines).
- `lem:radial-compactness` with the `C¹` clause (the kernel's `s`-derivative is the same integrand times `(w−ε²)/ξ_c`).
- `gt:7.5` (blow-up limit via `hb_uniqueness`, which exists).

**M3 Headline C′: strict gap `thm:intro-gap` (ii) (M–L).**
- Laplace limit L.6 (Stirling and majorants); compactness for `p_c`, `q_c`; `o(c^{1/3})` offsets and the infimal
  radius; the one-profile bound `−u_LP/β₁` (`prop:ce-one-profile`). Downstream (`ShellHBData`, `even_m_laplace_sign`,
  `OddShellFamily`) exists. Needs only M2.

**M4 Upper O-chain at one level (shared by everything below; L, technical core).**
- U.2 for `{f₁, g₁, g₁'}`, U.3, GT.2a (on its Fourier-side hypotheses; `GT.1` symbol bounds and `O4QuotientBound` taken as hypotheses), O.5, O.6, O.11ak (Mellin-lift hub), O.9′ at `m = 1`.
- O.3(2)/U.3(3): real-line subtraction of the `x^{−3/2}` tail, two integrations by parts and the Fresnel integral (no
  Puiseux, no V-ray). U.1 only in its closed-half-plane form.
- O.4(2): Banach contraction for the cubic normal form (`ContractingWith.fixedPoint`), with the certified bound on the
  circle as an interval-arithmetic input; no branched cover or monodromy.

**Headline S: separation `gt:7.9c` (S–M after M2, M4).** `gt:7.5` + `C¹` compactness + one-level O.9′ give the slope
window; the intertwiner and its tail positivity exist (`HardyMellinIntertwiner`, `sign_separation_*`). No Langer chart,
no bootstrap.

**M5 Hankel lower half at one level (L).**
- Langer chart `gt:7.7b/c/p` (Rouché exists). `gt:7.7b` (0)-(iv) is done (`HankelLangerU/Y/Real/ChartMain`, formulated in `u = ζ²`, where `g(ζ) = s` is `K(u) = 12s/π²`, so no square roots or sign choices); the strip setup (`g`, `S̃` as series = `log(tan/..)`, exact inversion on `Re ζ = σ`) and `gt:7.7c` are done at the level of the local integral (`HankelStrip*`, `HankelLocalPhase/Density/Envelope/Holo`: Cauchy shift, Gaussian peak, connectors, envelope `(e71)` in `ũ`, entire in `ℓ = log π²ξ`); the gluing with the chart (`HankelChartInverse/LangerPsi/LangerPsiReal`), reality (`HankelWtConj`) and the transport/mass hypotheses `gt:7.7p` (`HankelTransport*`, constants `r_∞ = 2I₀c^{1/3}e^{-c/40000}`, lobe `e^{-1.7e-6 c}`: weaker than the paper's but exponentially small, which is all the compactness step uses) are done; TE.0 for type (I) is done (`HankelQuantC1`: `hankel_quant_c1_typeI`, with the cut bound by a shift trick on `typeII_disc_avg_bound`; `HankelQuantC1Feasible`: `hankel_quantC1_of_feasible`, the conclusion `QuantC1B2Holds (hankelPsi c f) u_T` for feasible `f`); strip data and the Hankel `BandReductionInstance` are done (`HankelStripData`...`HankelBandAssembly`, `hankel_band_reduction`); still open: the rest of this list, where S6a (the Hankel `BootstrapHBInstance` `hankelBootHB`: `HankelBoot*`, with explicit `r_∞` slack `70 R r_∞`, `k₀ = 9`, from the hypothesis `HankelYVAt`) and S6b (the Hankel window lemma `hankel_yv_at : HankelYVAt hankelWindowC 10¹⁴`, `YVEnvBound (hankelPsi c f) c R L'` from `hankel_band_reduction`, `HankelWindow*`) are done; S7 is done (`hb_thresholds_lower : HbThresholdsLower`, `HankelThresholds`, via the second-order chart expansion `HankelChartSecond`). The Type (I) cut bound follows by subharmonic averaging as in Step 0 of
  TE.0, so the separate `Re ζ = c^{−1/3}` contour shift can be skipped in Lean.
- TE.0 at one level: adapt `teb_quant_c1_typeII` (already a compactness argument) to Type (I). This is non-effective,
  which is fine for Lean; the TeX keeps the effective version (Paper II needs it).
- TE.3 Hankel window (`teb:mellin` (2)-(3), open; the `BandReductionInstance` for part (1) is done); discharge the `BootstrapCore/Instance` fields starting from the
  general-weight bootstrap of Paper II (`ModularBootstrap/FixedWeightBand/BootstrapW*`, `BandBoundW*`), which already
  generalises the Virasoro `ArcBounds`/`QuadratureBounds` instance; do not refactor the Virasoro files. L.2/L.6 at one
  level. (Paper II's Langer chart and Mellin strip are different objects from the Hankel ones here; no overlap.)

**Headline A, `gt:7.9`:** M2 + M4 + M5 + the Euclidean reduction (BCK/CG, averaging, finite `d` via E.1; M).

**M6 CE upper, `thm:ce-hb-lift` at `m₀ = 1` with the convolution source (M).**
- Source `S_c = ∫₀^∞ w_c(y) g₁(u+y) dy`: product formula for its twisted transform, symbol bounds of the weight, far
  transfer GT.3b by Fourier–Sobolev, pre-edge bounds from the single-term Gaussian identity (exists:
  `airySquare_gaussian_transform`).
- `thm:ce-post-edge` and `cepe:general` stated for a general source; hb-lift assembly (seed mass `m₀ = 1` exists); lift
  to `Euc d`. This gives `hhi`.
- *Dependency list (audit of the Lean tree).* Proved and reusable: the Mellin lift of any `HasU2` seed
  (`liftSymbolData_of_hasU2`, `liftPhi_mellinLiftData`, `lift_edge_repr`, `exists_isHankelEigenfn_of_lift`), the
  seed mass and floors (`hb_seed_mass_exists`, `hbSeedSpec_airy_witness`), the B-spline multipliers and main-edge kernel
  (`MellinMainKernel`), reflected-line and dual-phase bounds (`gt2b_reflected_combined`, `o3_dual_bound`), far transfer
  (`gt3b_far_fourier_transfer`), the middle band (`middle_transfer_gt1`, conditional on `O4QuotientBound` and the `GT.1`
  bounds), the pre-edge criterion (`preEdge_general_pos`), `airySquare_gaussian_transform`, `HasU2` for `g₁` and
  `ceG1`, the radial Hankel transform on `Euc d` (`fourier_radial_hankel`, `integrable_radialLift_iff`). Missing, in
  order of use: (1) the convolution source `S_c` and Lemma `O.12` items (1)-(7) (`ceo:conv`; nothing exists, items (1)-(3)
  and the weight bounds `(ceo:conv.4)`-`(ceo:conv.5)` are scalar, item (7) needs `T_c` and the `FG.3` transfer
  operator, which exist); (2) `thm:ce-post-edge`, assembling `GT.2a`, `GT.2b` and (7) (not in Lean); (3) the two-seed
  lift `f[S, D]` as a pair, i.e. `h`, `ĥ` as the `σ = ±1` Hankel eigenfunction lifts of `(D ± S)/2`, with finite mass
  for seeds outside the `airySeedU2` span (`iMain_add_iDual_tail` and `exists_hankelEigenfn_lift` cover only that span,
  so the general-seed tail and mass bounds must be redone from `lift_edge_repr`); (4) the physical sign `u1co:O6` for the
  seeds `F_c` and the reflected seed `-S_c` (the `su/upper` lane has `o6_positivity`, conditional on the same
  `MiddleBandInputs` as `hb_thresholds_upper`), with tuning of `η_c` (`h(0) = ĥ(0) > 0`); (5) the pre-edge hypotheses
  for `D_c` from `ℒ_y(-G_Ai) > 0` (compact range) and the `u^{-3/2} e^{-4u^{3/2}/3}` tail; (6) the Euclidean lift of the
  Hankel profile to a radial continuous `L¹` pair with `ĥ ≥ 0` and `h ≤ 0` beyond the radius (the shell conditions are
  vacuous for `N = Ai`, `m = 1`, so only the final radius `R²/2 ≤ d/(2π²) - (t₁/β₁)(d/2)^{1/3} + K₀` and the offsets
  `|r| ≤ R_off` bookkeeping remain). Steps (1)-(2) need nothing from M4; (4) and the `GT.1`/`O4` inputs of (2) are the
  M4 interface, so the assembly takes them as named hypotheses.

**M7 CE lower (M).** Shell reduction `m = 1`, `O(d)` averaging, and the Hankel lower half from M5 give `hlo`. Done (`CEShellReduction`): a normalised continuous `L¹` Cohn–Elkies pair `(h, r)` yields the anti-self-dual competitor `ĥ - h∘(-·)` (`g(0) = 0`, `g ≥ 0` on `‖x‖ ≥ r`, nonzero by the compact-support uncertainty principle), `radialProjection` makes it Hankel-feasible at `r²/2` for `c = d/2`, `ε = -1`, and `hb_thresholds_lower` gives `shell_reduction_m1_proved` and `shell_reduction_airy : ShellReduction ShellHBData.airy` (the shell constraints are vacuous at `m = 1`); the fields `hb_thresholds_lower`, `shell_reduction_m1` are dropped from `RadiiInputs`. General `ShellReduction D` for `m ≥ 2` is M8. Remaining for M7 is `ce_hb_lift_m1` (upper half), which needs M6 (convolution source, post-edge, lift to `Euc d`) and `hb_thresholds_upper` from M4 (O-chain); nothing there is a routine scalar lemma yet, so no Haiku briefs are queued.

**Headline B, `gt:7.12` + `gt:7.12a`, unconditional.** This completes `thm:intro-radii`.

**M8 All levels (L).**
- TE.0′ by the same compactness argument for all `(P, Q)` (`hb_uniqueness` exists); TE.2(4) instance; general
  `HBSeedSpec` (`gt:1.0pp`); multilevel L.2.
- This gives `thm:intro-hb`, general `thm:ce-hb-lift`, and `thm:intro-gap` (iii) with its odd-level examples (H.14a).

**Deferred (not on any headline path):**
- Route I (`thm:ce-lift`, GT.4 bands, PF.2/PF.5, `prop:ce-pre-edge`) and the Dirichlet-diagonal machinery it still uses
  (CR.1–4, O.11 diagonal lemmas, PF.2L, PF.T, W.0–W.6); all in the TeX supplement;
- SE.1–SE.5 general de Branges and `PW·PW`;
- Theorem 3.1(c) (tempered distributions);
- fold-tip universality instances;
- `gt:7.10` (owner-deferred);
- the Neumann shell `thm:ce-neumann` (two-sided O(1); its proof is still being moved from notes into the TeX).

**Not a cheap headline.** An "Airy-order `o(d^{1/3})` radius theorem at fixed δ" is not a shortcut: the fixed-δ U.3
route needs a seed with the two-sided fill (e38) that no exhibited seed satisfies, and the honest upper half is O.9′,
i.e. M4.

**Parallelism.** M1 runs alongside M0. M2 and M4 are independent. M3 needs M2 only. With two or three agents the order
is M0 ∥ M1 → M2 ∥ M4 → M3, Headline S → M5 ∥ M6 → M7 → M8.

## 6. Bookkeeping

- QIprojects `docs/lean_status.md` (section "Paper I sign uncertainty") and this repository's `THEOREM_MAP.md` are kept
  current at every merge to `master`; the status review below is refreshed every six hours.
- Every Haiku-written module gets a clean-context Sonnet review before it is merged; every large Sonnet development
  (shell gap, the O.3(2) estimate, the window translation, the Hankel chart/density/transport, O.11ak) has had one.

## 7. Status review (2026-11-24, reasoner `master` after S4)

Size: `SignUncertainty` 133 files and about 39.8k lines, `CohnElkies` 63 files and about 52.7k lines. No placeholder
proofs, no custom axioms. The four headlines in `Headlines.lean` are still **conditional**, now on six inputs:
`hb_thresholds_lower`, `hb_thresholds_upper`, `shell_reduction_m1`, `ce_hb_lift_m1`, `shell_reduction`, `ce_hb_lift`.

| milestone | state |
|---|---|
| M0 skeleton | done |
| M1 classical leaves (Bessel, Weber, Laguerre modes, odd-`d` radial Fourier, `O(d)`/sphere averaging) | done |
| M2 Hankel layer (`gt:7.4`, `lem:radial-compactness`, `gt:7.5` input) | done |
| M3 strict gap, extraction half (`hankelShellGapLimit_proved`) | done; the origin floor and `u_* ≤ t_m` are not on its path |
| M4 upper O-chain | done: U.2, U.3(3)/O.3(2) = `(e4)` (uniform in seed coefficients), `(e3)`, O.4, `O.5(1)` = `(e5)`, O.11ak existence form, GT.2a: assembly `middle_transfer_gt1` (`MiddleBandTransfer`; outer pieces, `τ(εu)` substitution, `(e7)`/`(e8)`, regions), conditional on the named hypothesis `O4QuotientBound L` (`M_F ≤ 0.13`, interval certificate of `O.4`) and on the `GT.1` symbol bounds for `W(v) = liftSymbol X δ₀ m (v I)` as hypotheses. Also `O.5(2)` = `(e6)` (`o5_e6_airySeed`), `O.6` (`o6_positivity`, `O6Est`) and `O.9′` at `m = 1` (`hbThresholdsUpper_of_inputs : MiddleBandInputs 4 → HbThresholdsUpper`, i.e. `hb_thresholds_upper` conditional on the two named hypotheses). Open: `Gt1BasisInput m` (`GT.1` for the spline-multiplied basis seeds `f₁, g₁, g₁'`; the abstract-seed half `gt1Bounds_liftW_of_seed` and the Schwartz side are done, remaining: the three-phase tail form of the seeds), discharge of `O4QuotientBound L` for `0 < L ≤ 0.002` (interval certificate), after which `hb_thresholds_upper` is unconditional |
| M5 Hankel lower half | S1–S5 done (Langer chart, local density, tail and transport, type (I) compactness `hankel_quantC1_of_feasible`, strip data and `hankelBandInstance`/`hankel_band_reduction` = `teb:mellin` (1) only). S6a done (`hankelBootHB`: the `BootstrapHBInstance` at a good circle, from the window hypothesis `HankelYVAt`). S6b done (`hankel_yv_at : HankelYVAt hankelWindowC 10¹⁴`, the window lemma `teb:mellin` (2)-(3)). S7 done (`hb_thresholds_lower : HbThresholdsLower`, proved for both eigenvalues; `HankelChartSecond`, `HankelThresholds`). M5 is complete |
| Headline S (`gt:7.9c`) | needs `hb_thresholds_upper` (M4 end) |
| M6, M7, M8 | M7 lower half done (`shell_reduction_m1_proved`, `shell_reduction_airy`); M6 (CE upper, convolution source; gives `ce_hb_lift_m1`) needs M4, not started; M8 is the multilevel generalisation |

Critical path: M5 S6–S7 and TE.3 (2)-(3) (about 4–5k lines) in parallel with the M4 tail (GT.1 inputs for GT.2a, O.5(2), O.6, O.9′: about
6–8k lines), then M6 and M7 (M-sized each) and M8. Two Sonnet agents run these two lanes; Haiku agents implement the
routine statements the Sonnet agents queue.

Coverage gaps against the TeX that are recorded rather than closed:
- the tail exponent of `7.7p`: Lean `c/40000`, TeX `2·10⁻³c` (and two notes quoting consequences); the later steps only
  need `e^{-κc}`;
- `(e5)` is proved for `c ≥ 32768` (TeX `c ≥ 200`); no later use needs the smaller range;
- `(e4)`: the identification `γ₀ = c_s^{1/2}2^{2/3}π^{-1/2}β_∞` and the `L ≥ L₀` claim of `O.3(2)`;
- O.11ak: `f(0) = W(c^{1/3}) + σW(0)`, the fixed-`c` form with the kernel in `L¹`, general seeds;
- `7.7p (d)`: the explicit cut-crossing constant `3e^{1.5R₁+1.37R₁²}` (Lean has an effective but different constant) and
  the two-level `C¹` stability (`α ≠ 0`);
- Theorem H.14: the origin-floor clause and the endpoint case `u_* = t_m`.

Environment notes for the agents: single `lake build` slot pairs through `scratch/lslot.sh`; a hardlinked stale `.olean`
shows as "Unknown identifier" or "Application type mismatch" for something that exists: delete that module's build
files and rebuild; build outputs of reasoner modules outside the closure of `CohnElkies` and `SignUncertainty` were
deleted to free disk, so importing an outside module triggers a one-time rebuild.
