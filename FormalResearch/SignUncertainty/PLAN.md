# Paper I (Fourier sign uncertainty, Cohn-Elkies) - Lean plan

Source: QIprojects `CFT/sign_uncertainty/paper/` (`sign_uncertainty_core.tex`, the supplement parts) and the three
`CFT/common/` files it `\input`s (`airy_poisson.tex`, `clark_airy.tex`, `two_edge_bootstrap.tex`), read at QIprojects
`origin/main` `f4cc9812c` (2026-11-25). Lean state: reasoner `master` `2556a80`. Reader-facing status:
QIprojects `docs/lean_status.md` (section "Paper I sign uncertainty"). This file says what is true now; history is in git.
Wording: "proved" means a Lean theorem on `master` with the declaration named; "stated" means a Lean `def`/`Prop` or a
hypothesis structure with no proof; "proved modulo fields X" means a theorem whose hypothesis structure has the open
fields X. A `.lean` file existing is not verification.

## 1. Where we are

| fact | state |
|---|---|
| size | `SignUncertainty/` 237 files, 63.7k lines; `CohnElkies/` 65 files, 53.6k lines; `Special/Airy*` about 48k lines; `TwoEdgeBootstrap/` 4k; `Asymptotics/` 3k |
| placeholders | no proof placeholder and no declared `axiom` anywhere in `FormalResearch/` (grep). The headline theorems in `Headlines.lean` are guarded by `#guard_msgs` to `[propext, Classical.choice, Quot.sound]`; the `O4CertRun*` boxes use `decide +kernel` (no `native_decide`) |
| last recorded full build | `lake build FormalResearch.SignUncertainty FormalResearch.TwoEdgeBootstrap`, 9,269 jobs, about 9 min (audit of 2026-11-23; not re-run for this documentation pass) |
| paper headlines | three introduction theorems: `thm:intro-radii` (five-term radii), `thm:intro-hb` (bounded remainder at every fixed level), `thm:intro-gap` (CE thresholds at prescribed shells) |
| unconditional headline in Lean | none |

### 1.1 Headline status: paper statement against Lean statement

| paper | Lean (`Headlines.lean`) | matches the paper? | open inputs |
|---|---|---|---|
| `thm:intro-radii` (i)-(iii): five-term bounds for `T_c^eps`, `A_sign^eps(d)`, `r_CE(d)`, density formula | `thm_intro_radii`, `_sign`, `_ce`: the `O(1)` Airy-order law for `A_sign^+-(d)`, `r_CE(d)` for all `d >= 2` and the volume bound up to constants and `O(1)` in the log | **No: weaker.** It has the shape of `thm:ct-upper` (iii) and `gt:7.12a` only; the five-term statements `eq:intro-constant-sharp`, `eq:intro-radius`, `eq:intro-density` are not stated | `RadiiInputs`: `ce_hb_lift_m1` (= `CeHbLift ShellHBData.airy`, proved from the open `CeHankelPair`). Its other field `hb_thresholds_upper` is the theorem `hbThresholdsUpper` (`HbUpperM1`), kept as a field only because `HbUpperM1` imports `Headlines` (housekeeping, S: move the radii headline below `HbUpperM1` and drop the field); `hb_thresholds_lower` is a theorem |
| `thm:intro-hb` | not stated | - | one-level halves exist (`HbThresholdsLower`, `HbThresholdsUpper`); all-level `(P,Q)` is M8 |
| `thm:intro-gap` (i)-(iv) | `thm_intro_gap_i`, `_ii`, `_ii_even`, `_iii` for a configuration `D : ShellHBData` | (i), (ii) yes (offsets as in the paper); (iii) only for strict Laplace positivity (`0 < airyLaplace (-G) y`), the paper allows weak positivity with tangencies; **(iv) not stated** | `ShellGapInputs D`: `shell_reduction`, `ce_hb_lift`. (ii) and (ii)-even do not use them (`ShellGapInputs.shell_gap_limit` ignores its argument), so they are proved; the argument is a leftover |
| none (deleted from the paper) | retired, not a headline: `separation_neg_two_div_pi_sq` (`SignSeparationLimsup.lean`, formerly `thm_intro_separation` in `Headlines`): `limsup (T_c^{+1}-T_c^{-1}) <= -2/pi^2` | superseded by `eq:ct-split` (section 5) | none: `separation_neg_two_div_pi_sq_unconditional` (from `separationInputs_holds := ⟨hbThresholdsUpper⟩`) |

Open inputs, counted once: `ce_hb_lift_m1` (M6), `shell_reduction` for `m >= 2` (M8), `ce_hb_lift` for `m >= 2` (M8).

### 1.2 What is closed and reusable

- The Airy base (A1, A2): Theorems D, Q, B with their equality cases, Clark and Hermite-Biehler quadrature, `hb_uniqueness`, Airy PWS (a)<=>(b).
- The Hankel layer (B1, B2): the concrete real-order Bessel kernel (`hankelKernelData`, unconditional), `gt:7.4`, `radial_compactness`, the Euclid-Hankel dictionary in every integer `d >= 2` (`hankel_euclid_dictionary`), `gt:7.9a`, `gt:7.9b`.
- The one-level Hankel thresholds (C2, C3, B3): `hb_thresholds_lower` (`HankelThresholds`; via the Langer chart, transport, band reduction, window lemma and `hankelBootHB`) and `hbThresholdsUpper` (`HbUpperM1`, from `o6Bricks_holds`, `gt1BasisInput` and `o4QuotientBound`: 12,800 kernel-checked interval boxes).
- Shell extraction and the one-profile problem (E1): `hankelShellGapLimit_proved`, `shellGapLimit_of_hankel`, `one_profile_*`, `even_m_laplace_sign`, `shell_reduction_airy`.
- Cohn-Elkies radius layer (D2): `ce_quadratic_dimensions` (finite dimensions), `ce_schwartz_radius_eq_L1_radius`.
- M6 leaves (D1): the convolution source `ConvSource*` (`convS_bounds`, `ConvTailData`), `ceLift_pair`, `ceHankelPair_of_eigenfns`, `ceLift_tune`, `ceLift_physical` (proved modulo the fields of `CeSourceFamily`), `ce_hb_lift_airy_of_hankelPair` (proved modulo `CeHankelPair`), `preEdge_general_pos` (modulo `PreEdgeGeneralData`).

### 1.3 Recorded caveats

- Hypothesis packages of the superseded coherent-square route (Route I: `GT4CoverageBands`, `MovingDiagFarTail`, `MacroscopicTransferPackage`, the `Cardinal*`, `ClosedResolvent`, `ResolventAverage`, `MovingDiagonalSource` files, and the `hNicholson`, `hBesselRatio` fields in `CardinalSymbolBounds`) are no longer cited by the paper (Route I left the paper for `CFT/sign_uncertainty/notes/`). Per the old audit (2026-11-23, not repeated) they have only toy witnesses. Whether `M10` reuses any of them (`ceo:O11n.7`, `ceo:gauss.2` are cited by `constant_terms_upper.tex`; `AiryGaussianTransform` serves them) must be checked before anything is archived.
- `ce_radius_airy_order_of_bounds` (`CohnElkiesRadius`) is only a gluing step: its hypotheses `hlo`, `hhi` are the two halves.
- Differences from the TeX that later steps do not need: the tail exponent of `gt:7.7p` is `c/40000` in Lean and `2e-3 c` in the TeX; `(e5)` is proved for `c >= 32768` (TeX `c >= 200`); the deep-lobe bound of `radial_compactness` uses `g(sigma) < 4/3 sigma^2`; the middle band cuts in `tau`, not `theta`; `hankel_band_reduction` uses `b = 1/100` (paper `0.012880`) and is non-vacuous for `eps = -1` only; `hb_thresholds_lower` has non-sharp constants and `c_0 >= 10^14`.
- Statement gaps recorded rather than closed: `(e4)` identification `gamma_0 = c_s^{1/2} 2^{2/3} pi^{-1/2} beta_inf`; the `L >= L_0` claim of `O.3(2)`; `O.11ak` in fixed-`c` `L^1`-kernel form; `7.7p (d)` cut-crossing constant and two-level `C^1` stability; Theorem H.14 origin-floor clause and the endpoint case `u_* = t_m`.

## 2. Priority order: the headline theorems first

**Rule (owner, 2026-11-25): work goes to the paper's headline theorems first; anything not on a headline path waits.** Priority:
1. **Tier 1, `thm:intro-radii` (five terms), the main result:** M11 -> B3 -> C1 -> F1 -> F2 -> F3 -> density (2.1). This is M10 and now the main lane.
2. **Tier 1, the other two headlines:** `thm:intro-gap` (2.3), whose (i)-(iii) reuse M6 and M8, and `thm:intro-hb` (2.2, M8).
3. **Tier 2, after the headline paths:** M6's `CeHankelPair` packaging beyond what F2 and `thm:intro-gap` (iii) use (it only completes the interim `O(1)` Lean headline); housekeeping (restating `thm_intro_gap_ii`, dropping the import-order field `hb_thresholds_upper` from `RadiiInputs`, origin-floor and endpoint clauses); constant-sharpening of proved leaves; remarks; Route I leaves.

Package ids are from section 6.1, milestones from section 3. Nothing in this section is formalised unless section 6 says so.

**The Lean headline is not the paper headline.** `thm:intro-radii` is the five-term theorem `thm:ct-upper` (i)-(ii) plus the density corollary. Its proof (`constant_terms_lower.tex`, `constant_terms_upper.tex`, `constant_terms_five.tex`) does not cite `thm:ce-hb-lift` or `thm:ce-post-edge`; the five-term CE radius is built directly (`fct:main-ce`, `fct:ce-band`, `fct:ce-preedge`). It does reuse route-II leaves: `constant_terms_upper.tex` cites `ceo:conv` (4) (the symbol-derivative bound, as a method), `cepe:PE3`, `ceo:gauss.2` and `ceo:O11n.7`. So **M6's lift (`CeHankelPair`, post-edge, packaging) is not on the path of the paper's `thm:intro-radii`, but D1's convolution-source symbol bounds and pre-edge estimates (`ConvSource*`, `PreEdgeCriterion`) are F2 inputs**. It completes the interim Lean headline `thm_intro_radii` (the `O(1)` law) and is the `m_0 = 1` case of `thm:ce-hb-lift`, which `thm:intro-gap` (iii) needs. `thm:ct-upper` (iii) itself follows from (ii) and `thm:ce-gaussian` (finite dimensions), as the TeX proof says.

### 2.1 `thm:intro-radii` (five terms): M11 -> B3 -> C1 -> F1 -> F2 -> F3 -> density

1. **M11**, `u1cl:main` (S): assemble `hb_thresholds_lower` and `hbThresholdsUpper` at one level. Used by `constant_terms_lower`.
2. **B3**: `u1cl:langer` (Lemma L.2, S-M; a corollary of `gt:7.7b` (iv), already in Lean) and the clauses of `gt:7.7p` (d) that the lower bound cites (cut-crossing constant; `gt:7.7p` is cited ten times in `constant_terms_lower`).
3. **C1**: `uct:admiss` (Lemma T.8, M) and `ceo:O11ak` for general seeds (M; `exists_hankelEigenfn_lift_general` exists modulo `ConvTailData`). Both are used by `constant_terms_upper`.
4. **F1** (L): `ct:outer` first (it is also the input of F2), then `ct:dual-id`, `ct:cfu`, `ct:boas`, `ct:dyadic`; gives the five-term lower bound and the lower half of `eq:ct-split`. Inputs already in Lean: `mat:T1`, `mat:T4`, `gt:7.7b`, `gt:7.7c`, `radial_compactness`, `airy_defect_bound`, `hb_thresholds_lower`.
5. **F2** (L, largest): the `uct:*` lemmas (`outer-growth`, `airy-trans`, `pos-floor`, `strip-split`, `bump-est`, `seed-asymp`, `gen-preedge`), then the `fct:*` chain (`comp-D`, `phikill`, `warp-asymp`, `splitting`, `bump-5`) to `fct:main-hankel`; then `fct:ce-band`, `fct:ce-preedge` (with `uct:ce-band`) to `fct:main-ce`. Inputs already in Lean: `u1co:O3`-`O5` at one level, `airySquare_gaussian_transform`, `lobe_saddle_asymptotic`, `cel:L3a`/`L4`/`L7`, `mat:T1`-`T4`.
6. **F3** (S): `thm:ct-upper` (i), (ii) with the reductions `hankel_euclid_dictionary`, `intertwiner_feasible`, `ce_schwartz_radius_eq_L1_radius`, `hankelT0_eq_hankelT`; (iii) from (ii) and `ce_quadratic_dimensions` (or from the Lean `thm_intro_radii` once M6 closes).
7. **D2**: `gt:7.12a` exact density `eq:ce-density-exact` (S), then `thm:intro-radii` (S).

Steps 1 to 3 are independent. F2 needs from F1 only `ct:outer` (the outer function `G_eps` and its phase `theta_eps`, cited nine times in `constant_terms_upper`); `ct:dual-id`, `ct:boas`, `ct:dyadic` are lower-bound only, and the upper bounds cite `thm:ct-lower` only to combine into two-sided statements, so after `ct:outer` the two bounds proceed in parallel. The sign-radii half of (ii) needs F1 and `fct:main-hankel` only; the CE half needs `fct:main-ce`.

### 2.2 `thm:intro-hb`: A3 + B3 + C2 (all levels) -> C3 (M8)

1. **A3**: `TE.0'` for polynomial `(P,Q)` as a converter into `ChartCompactness` plus the shared rigidity theorem (agreement with the FoldTip lane, section 5); Hankel `BootstrapHBInstance` at every level.
2. **B3**: `u1cl:langer`.
3. **C2** (L): `U.2`, `U.3`, `GT.1`, `O.3`-`O.6` for the rational-Airy seeds of a general `(P,Q)`; `lem:hb-seed-mass` and a witness `HBSeedSpec` at every level.
4. **B1**: `gt:7.5` for general `(P,Q)`.
5. **C3**: `u1cl:multilevel` (both halves, with the `f(0) = 0` clause); then `thm:intro-hb` (S).

### 2.3 `thm:intro-gap`

- (ii): proved in the Lean statement. Housekeeping (S): restate without the unused `ShellGapInputs` argument, add the origin-floor clause and the `u_* = t_m` endpoint case of `thm:ce-physical-profile`.
- (i): `ShellReduction D` for `m >= 2` (E1, M): needs `u1cl:multilevel` lower half (section 2.2) and the radial projection already in `CEShellReduction`.
- (iii): M6 (D1), then `thm:ce-hb-lift` at every level with weak Laplace positivity and tangencies (M8), `thm:ce-canonical-iff` (E2) and the Laplace-positive odd families of `thm:ce-odd-family` (E1).
- (iv): E2 (M9: `thm:airy-square-attained`, `thm:ce-airy-transfer`, `thm:ce-canonical-iff`, `rem:airy-even-deep-gap`), `cor:ce-schwartz-shells` (D2) and `thm:ce-shifted-lift` (route-II machinery at shifted nodes). E2 needs only M3, so it can start now.

### 2.4 Next concrete packages (headline paths only)

1. **Start now (tier 1, `thm:intro-radii`):** M11 `u1cl:main` (S), then `u1cl:langer` (S-M); in parallel C1's `uct:admiss` (T.8, M). None needs another package.
2. **Then:** F1's first block, `ct:outer` and `ct:dual-id` (`constant_terms_lower.tex`), on proved inputs only (`mat:T1`, `mat:T4`, `gt:7.7b`); `ct:outer` unblocks F2.
3. **Continue, scoped to what the headlines use:** M6 step (a), the `CeSourceFamily` instance for `convSource` (the `ConvSource*` symbol bounds and pre-edge estimates also feed F2), and the `m_0 = 1` lift that `thm:intro-gap` (iii) needs.
4. **Second headline lane once two slots are free:** `thm:intro-gap` (iv) through M9 (E2), beginning with `thm:airy-square-attained` (needs only proved inputs: `airyNC_quadrature`, `airyAiC_logDeriv_mittagLeffler`).

Tier-2 items are not started while a tier-1 package is unstaffed.

## 3. Milestones

Names M0-M11 are kept. Size classes as in 6.1.

| milestone | content | packages | state | remaining |
|---|---|---|---|---|
| M0 skeleton | concrete definitions, headline statements, input structures (`RadiiInputs`, `ShellGapInputs`) | H | done | housekeeping (S): restate `thm_intro_gap_ii` without `ShellGapInputs`; decide the fate of the Route I leaves (section 1.3) |
| M1 classical leaves | real-order Bessel, Laguerre modes, radial Fourier transform on `Euc d` (even and odd `d`), Airy base | A1, A2, B2 | done | - |
| M2 Hankel layer | `hankelKernelData`, `gt:7.4`, `radial_compactness` | B1 | done | `gt:7.5` instance (S-M, with M8) |
| M3 strict gap, extraction half | `hankelShellGapLimit_proved`, one-profile problem, `even_m_laplace_sign` | E1 | done | origin-floor clause, endpoint case (S) |
| M4 upper O-chain at one level | `U.2`-`O.6`, `O.9'` at `m_0 = 1`; `o4QuotientBound` | C1, C2 | done | - |
| M5 Hankel lower half at one level | Langer chart, transport, band reduction, window, `hankelBootHB`; `hb_thresholds_lower` | B3, C3, A3 | done | `u1cl:langer`, `gt:7.7p` (d) clauses (S-M, M8 prerequisite) |
| M6 CE upper, route II at `m_0 = 1` | `CeHankelPair`, hence `ce_hb_lift_m1` | D1 | in progress; `CeHankelPair` NOT proved | (a) `CeSourceFamily` instance for `convSource`; (b) `thm:ce-post-edge` with `cepe:general` for `D_c`; (c) packaging, refactor `ceLift_physical` to expose both edge representations (L) |
| M7 CE lower, shell reduction at one level | `shell_reduction_airy` | E1, D2 | done at `m = 1` | upper half is M6 |
| M8 all levels | `TE.0'` general, `u1cl:langer`, multilevel thresholds (`u1cl:multilevel`), `ShellReduction D`, `CeHbLift D` with weak positivity, positive odd families, `gt:7.5` general | A3, B1, B3, C2, C3, D1, E1 | not started | L; starts with a dependency list once M6 is merged |
| M9 Airy-LP core | `thm:airy-square-attained`, `thm:ce-airy-transfer`, `thm:ce-canonical-iff`, two-level Rayleigh, shifted lift, `cor:ce-schwartz-shells` | E2, D2 | planned, not started | L; needs only M3 |
| M10 constant terms | `thm:ct-lower`/`thm:ct-upper` five terms, density `eq:ce-density-exact`; carries the paper's `thm:intro-radii` | F1, F2, F3, D2, C1 | planned, not started; no Lean exists | L, constants non-effective; the main lane: it carries the paper headline (owner rule, section 2) |
| M11 Hankel two-sided `O(1)` | `thm:hankel-one-two` from the two proved halves | C3 | planned | S |
| Headline S (retired) | `gt:7.9c` separation `-2/pi^2`, deleted from the paper | - | retired from the headlines; proved unconditionally as `separation_neg_two_div_pi_sq_unconditional` (`SignSeparationLimsup.lean`) | none; the sharp `-1/pi` is a corollary of M10 |

Not on any path and not planned: `gt:7.10` (owner-deferred), `thm:ce-neumann`, Route I (`thm:ce-lift`, GT.4, PF.2/PF.5, the Dirichlet-diagonal chain; outside the paper), general de Branges SE.1-SE.5 and `PW*PW` characterisations, Theorem 3.1 (c) for tempered distributions. Fold-tip instances belong to the FoldTip lane (package G).

An "Airy-order `o(d^{1/3})` radius at fixed `delta`" is not a shortcut: the fixed-`delta` `U.3` route needs a seed with the two-sided fill `(e38)` that no exhibited seed satisfies.

## 4. Strategy and working rules

- **Skeleton first, and inputs must shrink.** Each headline is proved from one input structure whose fields are, one to one, TeX theorems; progress is the number of open fields. A module is merged only if it discharges or shrinks a field, or is a package of section 2 on a critical path; toy non-vacuity witnesses are not progress.
- **No second proof of a closed route.** Before opening a step run `tools/find_result.py` in QIprojects and check this file's coverage table (section 6); an `OPEN` in a PR state is not evidence that nobody has proved it.
- **Conditional results are named as such.** A statement that takes an input structure says so in its docstring and in `docs/lean_status.md`; unused arguments (as in `thm_intro_gap_ii`) are removed.
- **Process.** The manager alone edits the status rows of this file; agents report in handoffs, `THEOREM_MAP.md` and umbrella rows. A clean-context reviewer builds the headline module of its step, not the umbrella; the umbrella build is the manager's after each merge round, merges are batched. At most two Sonnet lanes, three Haiku agents and one reviewer build at once (two build slots); every Haiku module and every large development gets a clean-context review before merge. New worktrees are made with `scratch/mkwt.sh`, which deletes build outputs whose source differs from the copied build: a hardlinked stale `.olean` shows as "Unknown identifier" or "Application type mismatch" for something that exists.
- **Paper-side updates after a milestone.** Update the manuscript appendix that names Lean declarations, the `CORRECTIONS.md` lines for any stated result changed by the formalisation, and `docs/lean_status.md` (it still says the headlines carry "six open results"; the count is three, section 1.1).

## 5. Owner decisions and cross-lane agreements

**Decided (owner, 2026-11-25): the separation headline is retired.** The old `thm_intro_separation{,_hankel,_radii}` (`limsup (T_c^{+1}-T_c^{-1}) <= -2/pi^2`, old `gt:7.9c`, deleted from the paper and archived in QIprojects `CFT/sign_uncertainty/history/notes/archived_sign_separation.md`) moved out of `Headlines.lean` to `SignSeparationLimsup.lean` as `separation_neg_two_div_pi_sq{,_hankel,_radii}`, and its only input is now supplied (`separation_neg_two_div_pi_sq_unconditional`). It is not a headline and nothing new is built on it; `SignSeparation.lean` and `HardyMellinIntertwiner` stay as libraries (`gt:7.9a` reuses the intertwiner). The sharp form `T^+ - T^- -> -1/pi` is a one-line corollary of `eq:ct-split` once M10 is done, not a separate target.

**Decided (owner, 2026-11-25): headline theorems first.** M10 is the main lane (it carries the paper's `thm:intro-radii`); M6 continues only as far as F2 and `thm:intro-gap` (iii) need it; everything off a headline path is tier 2 (section 2).

**Agreements with the ModularBootstrap/FoldTip lane (Paper II plan, section 4).**
1. `HermiteBiehlerData` lives in the neutral module `SignUncertainty/HermiteBiehlerData.lean` (imports only `HermiteBiehlerUniq`); `RadialRigidity` re-exports it.
2. The base structure `ChartCompactness` (`compactness_subseq` plus site and tail positivity for an abstract setting) is owned by the fold-tip lane in a module importing nothing Hankel- or Virasoro-specific. It is **not on `master` yet**.
3. Paper I adds, without editing `RadialRigidity.lean`, a converter `RadialRigidityPackage -> ChartCompactness`, and plans M8's `TE.0'` (compactness for all `(P,Q)`) as a converter into `ChartCompactness` plus the shared rigidity theorem, not a second copy of the argument. Both start when `ChartCompactness` is on `master`.
4. The two rigidity proofs differ (profile compactness with Hermite-Biehler uniqueness here, vague limits of design measures there); only the interface is shared.
5. Langer charts and Mellin strips are separate objects in the two papers (Hankel/Bessel density `gt:7.7b/c/p` and `MellinStrip*` here; Virasoro comb density and `FixedWeightBand/Mellin*W` there). The Hankel `BootstrapHBInstance` follows the pattern of `FixedWeightBand/BootstrapW*`; Paper II does not refactor `ConcreteBootstrap/` or `TwoEdgeBootstrap/`, and Paper I does not edit `QuantC1Airy.lean`/`QuantC1Clark.lean` (Paper II's, imported here).
6. Fold-tip Theorem FT is part of Paper I (Section 4); its Lean code and plan are `ModularBootstrap/FoldTip/` and packages FT-0..FT-7 of `ModularBootstrap/PLAN.md` (package G, section 6.1). `lem:qual-compact` is not in Lean; it is the shared elementary step for `ft:L2` and the CE shell transfers (check `SignUncertainty/` before adding).

## 6. Coverage of the paper (reference)

Every stated result of Paper I is listed once: 152 results (3 introduction theorems, 119 `result` environments in `CFT/sign_uncertainty/paper/*.tex`, and 30 in the three `CFT/common/` files the paper `\input`s: `airy_poisson.tex` 16, `clark_airy.tex` 7, `two_edge_bootstrap.tex` 7). Aliased labels are one row, keyed by the first label. States are on `master` (`2556a80`): **done** 52, **partial** 40, **planned** 59, **not planned** 1.

A row is **done** when the label is proved in Lean for the stated hypotheses (any difference in constants is noted), **partial** when some parts or instances are proved and the missing part is named, **planned** when a milestone owns it and nothing is stated, **not planned** with the reason. placeholders/`axiom`: none anywhere in `FormalResearch/` (grep on `master`), so no declaration cited here depends on a placeholder; "proved modulo fields" always means a named hypothesis structure.

### 6.1 Packages

| pkg | package | TeX | results | done / partial / planned / not planned | remaining size | inputs still taken as hypotheses | depends on | milestone |
|---|---|---|---|---|---|---|---|---|
| **A1** | Airy-Poisson defect formula, quadrature, sign uncertainty at the first node | `common/airy_poisson.tex` | 16 | 15 / 1 / 0 / 0 | - | none | - | M1 |
| **A2** | Clark-Airy and Hermite-Biehler quadrature, two-node theorem, Airy PWS | `common/clark_airy.tex` | 7 | 6 / 1 / 0 / 0 | - | none | A1 | M1 |
| **A3** | Two-edge bootstrap (strip Poisson, edge oscillation, Riesz-Airy-Poisson bootstrap, `C^1` stability) | `common/two_edge_bootstrap.tex` | 7 | 1 / 6 / 0 / 0 | M-L (all-`(P,Q)` `TE.0'` as a converter into the shared `ChartCompactness`; Hankel HB instance at every level) | Stage A is an instance obligation: `BootstrapInstance`, `BootstrapHBInstance`, `BootstrapCore` fields. Discharged for the Hankel one-level problem (`hankelBootHB`) and for Paper II problems; not for general `(P,Q)` Hankel | A1, A2, B3 | M8 |
| **B1** | Hankel layer: Mellin strip, radial compactness, rigidity | `fourier_mellin.tex`, `general_theorems.tex` | 3 | 2 / 1 / 0 / 0 | S-M (`gt:7.5` instance and `(P,Q)` form) | `gt:7.5`: `RadialRigidityPackage` fields | A2 | M2 |
| **B2** | Euclid-Hankel dictionary, Hardy-Mellin intertwiner, origin constraint | `general_theorems.tex` | 2 | 2 / 0 / 0 / 0 | - | none | B1 | M1/M2 |
| **B3** | Langer chart, local density, transport, edge representation | `langer_transport.tex` | 5 | 2 / 2 / 1 / 0 | S-M (`u1cl:langer`, `gt:7.7p` (d), weighted-Mellin clause) | none (constants weaker than the TeX) | B1, C1 | M5, M8 |
| **C1** | Mellin-Airy toolkit and symbol transfer | `mellin_airy_toolkit.tex` | 11 | 6 / 4 / 1 / 0 | M (`uct:admiss`, general-seed `O.11ak`) | `ConvTailData` for general-seed `exists_hankelEigenfn_lift_general` | A1, B1 | M4, M6, M10 |
| **C2** | Upper O-chain at one level (`U.*`, `O.*`, hb-seed-mass, `O.9'`) | `u1c_o1_upper.tex` | 13 | 5 / 8 / 0 / 0 | L (all-level `(P,Q)` seeds) | none for `hbThresholdsUpper`; `m_0 = 1` only | A1, A2, B1, C1 | M4, M8 |
| **C3** | Hankel thresholds: one-level halves, multilevel theorem, two-sided `O(1)` | `u1c_o1_lower.tex` | 2 | 0 / 1 / 1 / 0 | L (all levels); S (`u1cl:main`) | none at one level | A3, B3, C2 | M5, M8, M11 |
| **D1** | Cohn-Elkies upper half, route II: convolution source, transfer, pre-edge, post-edge, lift | `ce_hb_lift.tex`, `ce_o1_route.tex`, `ce_o1_global_transfer.tex`, `ce_o1_pre_edge.tex`, `ce_physical_log_far.tex`, `ce_rate.tex` | 16 | 9 / 4 / 3 / 0 | L (instance of `CeSourceFamily` M; post-edge sign L; packaging S-M) | `CeSourceFamily` (tail, dual fields), `PreEdgeGeneralData`, open `CeHankelPair` | B2, C1, C2, E1 (`ShellHBData`) | M6, M8 |
| **D2** | Cohn-Elkies radius layer: finite dimensions, Schwartz vs `L^1` infimum, density | `ce_finite_bounds.tex`, `ce_radius.tex` | 5 | 1 / 2 / 1 / 1 | S-M | `ce_radius_airy_order_of_bounds` takes both halves as hypotheses (`hlo`, `hhi`) | B2 | M7, M9, M10 |
| **E1** | Cohn-Elkies shells: reduction, extraction, one-profile, odd families | `ce_shells.tex` | 7 | 3 / 4 / 0 / 0 | M (`ShellReduction D`); M-L (positive odd families) | `ShellReduction D` for `m >= 2`; none for the extraction and one-profile parts | B1, B2, C3 | M3, M7, M8 |
| **E2** | Limiting Airy program at prescribed shells (Airy-LP) | `ce_airy_lp.tex`, `ce_airy_lp_proofs.tex`, `ce_canonical_iff.tex`, `ce_two_level.tex`, `ce_shifted_witnesses.tex`, `airy_extremal.tex` | 23 | 0 / 0 / 23 / 0 | L (about 23 results; calibration: `ShellLaplaceBase` 1.9k + `OddShellFamily` 1.4k lines) | - | A1, A2, E1 (needs only M3) | M9 |
| **F1** | Five-term lower bound for the Hankel thresholds | `constant_terms_lower.tex` | 5 | 0 / 0 / 5 / 0 | L (calibration: the Virasoro lower half took about 29k lines) | - | B1, B3 (incl. `u1cl:langer`), C1, A3, M11 | M10 |
| **F2** | Five-term upper bound for the Hankel thresholds and the Cohn-Elkies radius | `constant_terms_upper.tex`, `constant_terms_five.tex` | 17 | 0 / 0 / 17 / 0 | L (17 results, several over 1,000 TeX lines; the largest single package) | - | F1 (`ct:outer` only: the strip outer function and its phase, cited 9 times), C1 (`uct:admiss`, general-seed `O.11ak`), C2, D1 (`cel:L*`, `ceo:gauss`, `ceo:O11n`, `ceo:conv` (4), `cepe:PE3`), A2 (`gt:3.1`) | M10 |
| **F3** | Five-term theorem `thm:ct-upper` (assembly and reductions) | `general_theorems.tex` | 1 | 0 / 1 / 0 / 0 | S | F1, F2 (parts (i), (ii)); `RadiiInputs` for (iii) | B2, D2, F1, F2 | M10 |
| **G** | Fold-tip universality (Theorem FT and the two-edge versions) | `fold_tip_universality.tex`, `fold_tip_two_edge.tex`, `fold_tip_two_edge_hb.tex` | 9 | 0 / 3 / 6 / 0 | owned by the ModularBootstrap/FoldTip lane (`ModularBootstrap/PLAN.md`, packages FT-0..FT-7) | violator family and chart coverage as hypotheses; `FTH4b` mismatch | A3, Paper II instances | FT lane |
| **H** | Introduction theorems | `sign_uncertainty_core.tex` | 3 | 0 / 2 / 1 / 0 | S per theorem after its inputs | `RadiiInputs` (open: `ce_hb_lift_m1`), `ShellGapInputs` (open: `shell_reduction`, `ce_hb_lift`) | see section 2 | all |

The "Lean today" column of each package (declaration families and size) is in 6.2 below, one table per package. Size classes: S < 500 lines, M 500-2000, L > 2000, for the remaining work, calibrated on existing files: `CEShellReduction` 227, `HankelThresholds` 147, `ShellLaplaceBase` 1,939, `OddShellFamily` 1,375, the whole one-level Hankel lower half (`Hankel*`) about 17.6k, `O4*` 2.7k, `ConvSource*` 3.2k, `ShellGap*` 2.7k.

### 6.2 Results by package

**A1. Airy-Poisson defect formula, quadrature, sign uncertainty at the first node** (`common/airy_poisson.tex`). Lean: `Special/AiryCft*` (about 8k lines), `AiryKernel*`, `AiryTransform*`, `AiryEnvelope*`, `Complex/Hardy*`.

| label | state | Lean today / note |
|---|---|---|
| `ap:E1` | done | `airyAiC_envelope` |
| `ap:E2` | done | `good_circle_exists`, `good_circle_airyAiC_ne_zero` |
| `ap:E3` | done | `airyEnv_add_real_le` |
| `ap:E4` | done | `airyPhi_norm_le` |
| `ap:thmD` | done | `airy_defect_bound`, `airy_defect_ball` |
| `ap:corD1` | done | `airy_quadrature` |
| `ap:lemU` | done | `airyQG` (unfolding `u = -z^2`) |
| `ap:lemH` | done | `hardy_integral_zero`, `hardy_value_le` (the inequalities used; Hardy spaces are not defined) |
| `ap:lemHp` | partial | `airyQ_mem_half`, `airyQ_pointwise_uniform` give the `f in L^1`, `s = 0` form; the shifted form `s > 0` is not stated |
| `ap:lemFR` | done | `hardy_arc_le` |
| `ap:thmQ` | done | `airyQ_defect_bound_int`, `airyQ_pointwise_sharp`, `airyQ_sampling`, `airyQ_hasSum_unc` |
| `ap:corQp` | done | `airyQ_vanishing_moment`, `airyQ_vanishing_moment_decay` |
| `lam:Q1` | done | `airyQ_hasSum_unc` |
| `lam:Q2a` | done | `airyKer`, `airyKer_eq_integral`, `airyKer_diag_le` |
| `lam:Q2` | done | `airyPW_reproducing`, `airyPW_parseval`, `airyClassG_PW_mul` |
| `lam:thmB` | done | `airy_sign_uncertainty`, `airy_sign_equality_iff`, `airyExtremal_attains` |

**A2. Clark-Airy and Hermite-Biehler quadrature, two-node theorem, Airy PWS** (`common/clark_airy.tex`). Lean: `Special/AiryPoly*`, `AiryThm47*`, `AiryClark*`, `AiryPws*`; `SignUncertainty/ClarkTwoNode`, `HermiteBiehlerUniq`, `HermiteBiehlerData`.

| label | state | Lean today / note |
|---|---|---|
| `gt:1.0` | done | `airyNC_good_circle` |
| `gt:1.0p` | done | `airyPQ_good_circle`, `airyPQ_good_circle_SE5` |
| `gt:1.0pp` | done | `airyPQ_hasSum_unc`, `airyPQ_tendsto_of_simple` |
| `lem:hb-uniqueness` | done | `hb_uniqueness`, `hb_two_node_l1_norm`, `airy_m1_uniqueness` |
| `gt:1.1` | done | `airyClark_hasSum_unc`, `airyClark_quadrature` |
| `gt:1.2` | done | `clark_two_node_uncertainty`, `clark_two_node_equality_iff` |
| `gt:3.1` | partial | `airyFtilde_norm_le` (a=>b), `airyPws_converse` (b=>a), `airyFtilde_laplace` (c=>b for `m in L^1`); (c) for tempered `mu` is not in Lean (needs Paley-Wiener-Schwartz for distributions) and no consumer on a headline path needs it |

**A3. Two-edge bootstrap (strip Poisson, edge oscillation, Riesz-Airy-Poisson bootstrap, `C^1` stability)** (`common/two_edge_bootstrap.tex`). Lean: `TwoEdgeBootstrap/*` (Stage B), `Complex/StripPoisson`, `Asymptotics/StirlingHalfInt`; instances in `SignUncertainty/Hankel*` and Paper II `ConcreteBootstrap/`, `FixedWeightBand/`.

| label | state | Lean today / note |
|---|---|---|
| `teb:quant_c1_hb` | partial | `hankel_quant_c1_typeI` (Hankel, type I, `alpha = 0`); Clark type II `teb_quant_c1_clark_typeII`; general polynomial `(P,Q)`: planned M8 as a converter into the shared `ChartCompactness` |
| `teb:quant_c1` | partial | Airy type II `teb_quant_c1_typeII` (Paper II file), Hankel type I `hankel_quantC1_of_feasible`; the remaining Clark cases are Paper II |
| `teb:bootstrap` | partial | Stage B proved from the instance structures: `teb_bootstrap_part1`-`part3`, `teb_bootstrap_hb`, `teb_weak_part1`; Stage A (building `(TE.4)`-`(TE.6)` from `(B1)`-`(B2)`) exists only as instances: `hankelBootHB` (Hankel, one level), Paper II fixed weight |
| `teb:kernel` | partial | `stripPoissonP_integral`, `stripPoissonQ_tv_le`, `stripPoissonCalQ_le` (kernel bounds, `Complex/StripPoisson`); the holomorphic representation is `StripBand/StripPoissonRep` (Paper II lane) |
| `teb:edge-osc` | done | `teb_edge_osc_interval`, `teb_edge_osc_tendsto` |
| `teb:mellin` | partial | part (1) `hankel_band_reduction` (and `StripBand/BandReduction`); parts (2)-(3) `hankel_yv_at`, `hankelBootHB` for the Hankel instance only |
| `teb:mellin_o1` | partial | `teb_mellin_o1_lower` from a `BootstrapInstance`; the Hankel one-level lower half is proved by `hb_thresholds_lower` without it |

**B1. Hankel layer: Mellin strip, radial compactness, rigidity** (`fourier_mellin.tex`, `general_theorems.tex`). Lean: `Mellin*`, `Radial*`, `DeepLobe*`, `ThreeLinesUnit`, `HankelBessel*`, `Special/Bessel*` (about 10k lines).

| label | state | Lean today / note |
|---|---|---|
| `gt:7.4` | done | `mellinStrip_reflection_of_re_lt`, `norm_mellinStrip_le_majorant`, `diffContOnCl_mellinW`, `three_lines_unit`; the description of `Re H` as a harmonic function is not formalised, only the majorant that is used |
| `lem:radial-compactness` | done | `radial_compactness` with its `C^1` clause (`deep_lobe_mass_thm`, `montel_rightHalfPlane`); the deep-lobe constant is weaker than the TeX |
| `gt:7.5` | partial | `radial_rigidity_lower_of_compactness` (one level, `eps = -1`, liminf); the abstract `RadialRigidityPackage` with `radial_rigidity_liminf`, `radial_rigidity_profile`, `radial_rigidity_origin` is not instantiated for the Hankel problem or for general `(P,Q)` |

**B2. Euclid-Hankel dictionary, Hardy-Mellin intertwiner, origin constraint** (`general_theorems.tex`). Lean: `Euclid*`, `SphereAverage`, `FourierCompactSupport`, `HardyMellinIntertwiner`, `Radii`, `HankelBesselLaguerre` (`hankel_euclid_dictionary` for every `d >= 2`).

| label | state | Lean today / note |
|---|---|---|
| `gt:7.9a` | done | `intertwiner_feasible`, `threshold_pos_le_neg`, `fourier_radii_pos_le_neg` |
| `gt:7.9b` | done | `hankelT0_eq_hankelT`, `laguerre_odd_mode`, `isRadialEigenfn_oddLaguerreMode_bessel` |

**B3. Langer chart, local density, transport, edge representation** (`langer_transport.tex`). Lean: `HankelLanger*`, `HankelStrip*`, `HankelLocal*`, `HankelTail`, `HankelTransport*`, `HankelEdge*` (about 6k lines).

| label | state | Lean today / note |
|---|---|---|
| `gt:7.7b` | done | `HankelLangerU/Y/Real/ChartMain` (`u = zeta^2` form), `HankelLangerIdentity` |
| `gt:7.7c` | done | `HankelLocalDensity`, `HankelLocalEnvelope` (envelope `(e71)`), `HankelLocalHolo` |
| `gt:7.7p` | partial | `hankel_tail_le`, `hankel_psi_neg_mass`, `HankelTransport*` for `c >= 3e6` with weaker constants (tail `c/40000`); the explicit cut-crossing constant and the two-level `C^1` stability (`alpha != 0`) of part (d) are not stated |
| `u1cl:langer` | planned | M8 (S-M): corollary of `gt:7.7b` (iv); no declaration yet |
| `u1cl:rep` | partial | `HankelEdgeRep`, `HankelStripInversion`, `HankelBandInstance` for the one-level Hankel problem; the weighted-Mellin clause (`u1cl:weighted-mellin`) is not stated |

**C1. Mellin-Airy toolkit and symbol transfer** (`mellin_airy_toolkit.tex`). Lean: `CohnElkies/Mellin*`, `AirySymbolTransfer`, `SeedSymbolDerivs`, `Gt1*`, `MiddleBand*`, `MellinLift*`, `Asymptotics/BinetRemainder` (about 25k lines).

| label | state | Lean today / note |
|---|---|---|
| `mat:T1` | done | `muBin_pos`, `binetDiff_norm_le`, `binetRem_iteratedDeriv_norm_le` (`Asymptotics/BinetRemainder`) |
| `mat:T2` | done | `mellin_strip_kernel_eq`, `norm_mellinK0_imag_le` |
| `mat:T3` | partial | parts (1), (3): `stripG_deriv_bounds`, `im_stripG_ge`, `im_stripG_ge_gaussian`; remaining parts not audited against the current TeX |
| `mat:T4` | done | `edgePhiDeriv_ge`, `edgePhiDeriv2_abs_le`, `edgePhiDeriv3_abs_le`, `m1_bound`, `m2_bounds`, `ceGamma_strictMonoOn` |
| `mat:T5` | done | `fourier_L1_le_sqrt_mul`, `fourier_L1_le_sqrt_mul_H1` |
| `cegt:GT1` | partial | `gt1BasisInput` (basis seeds `f_1, g_1, g_1'` times the spline multiplier, `m >= 3`); other seed families not stated |
| `cegt:GT1s` | done | `gt1s_scalar_airy_symbol_transfer` |
| `cegt:GT2a` | partial | `middle_transfer_gt1` for `HasU2` seeds (cut in `tau`, not in `theta` as in the TeX); the hypothesis `Gt1Bounds` is supplied by `gt1BasisInput` |
| `mat:T7` | done | `MellinLiftData.mellin_mellinInv`, `mellin_inversion_f` |
| `ceo:O11ak` | partial | `exists_hankelEigenfn_lift` (one-level seeds, `m >= 3`); `exists_hankelEigenfn_lift_general` (general seeds) takes the tail structure `ConvTailData` as a hypothesis; the fixed-`c` `L^1`-kernel form is not stated |
| `uct:admiss` | planned | M10 (M): only `constant_terms_upper` uses it; no declaration yet |

**C2. Upper O-chain at one level (`U.*`, `O.*`, hb-seed-mass, `O.9'`)** (`u1c_o1_upper.tex`). Lean: `CohnElkies/AirySeedFloors`, `AirySeedSymbols`, `PieceC*`, `HighBand*`, `DualBoundE3`, `CubicNormalForm*`, `O4*` (12,800-box certificate), `MiddleBand*`, `WindowTranslation`, `HbUpperM1` (about 25k lines).

| label | state | Lean today / note |
|---|---|---|
| `u1c:U1` | partial | `SeedSqrtForm` (`sqForm_*`, square-root form of the seed transforms) and `ElementaryIdentities`; the expansion on `Re w = 0` is not stated |
| `u1c:U2` | partial | `hasU2_airySeedU2`, `hbSeed_m1_hasU2`, `ceF1_symbolBounds`, `ceG1_symbolBounds` (one-level seeds and the `m_0 = 1` HB seed only) |
| `u1c:U3` | partial | `pieceC_main_term` (conditional on named hypotheses), `FresnelBranch`, `PieceC*`, `TwoIBPPhase`; the assembled statement for rational-Airy seeds is not in Lean |
| `u1c:U4a` | done | `airy_seed_integrals`, `ceG1_add_ceG1Deriv_pos`, `ceSb_lower_floor` |
| `u1co:O0` | done | `bspline_oscillating_floor` |
| `u1co:O1` | done | `bspline_floor_smoothing_gain` |
| `u1co:O2` | done | `o2_reflected_line_deriv_bound` |
| `u1co:O3` | partial | (1): `dual_phase_oscillatory_bound`, `iDual_bound_e3_airySeed`; (2) `(e4)`: `hb_estimate_airySeed_uniform` for one-level seeds; the identification `gamma_0 = c_s^{1/2} 2^{2/3} pi^{-1/2} beta_inf` and the `L >= L_0` claim are not stated |
| `u1co:O4` | done | `o4QuotientBound` (12,800 kernel-checked boxes), `o4_normal_form`, `CubicNormalFormH` |
| `u1co:O5` | partial | (e5) `window_translation_airySeed` for `c >= 32768` (TeX: `c >= 200`); (e6) `o5_e6`, `o5_e6_airySeed` |
| `u1co:O6` | partial | `o6_positivity` with `O6Est`; bricks discharged for the one-level seed by `o6Bricks_holds` (`m >= 3`) |
| `lem:hb-seed-mass` | partial | `hb_seed_mass_exists` for any `HBSeedSpec`; only the `m_0 = 1` witness `hbSeedSpec_airy_witness` exists |
| `u1co:O9p` | partial | `hbThresholdsUpper` (`m_0 = 1`, `N = Ai`); all-level `(P,Q)`: planned M8 |

**C3. Hankel thresholds: one-level halves, multilevel theorem, two-sided `O(1)`** (`u1c_o1_lower.tex`). Lean: `HankelThresholds` (`hb_thresholds_lower`), `HbUpperM1` (`hbThresholdsUpper`), `HankelBoot*`, `HankelWindow*`, `HankelQuantC1*`, `HankelBand*`.

| label | state | Lean today / note |
|---|---|---|
| `u1cl:multilevel` | partial | one level: lower half `hb_thresholds_lower`, upper half `hbThresholdsUpper`; all `(P,Q)` and the `f(0) = 0` clause: planned M8 (no `HbThresholds` declaration exists) |
| `u1cl:main` | planned | M11 (S): statement-level assembly of the two proved one-level halves |

**D1. Cohn-Elkies upper half, route II: convolution source, transfer, pre-edge, post-edge, lift** (`ce_hb_lift.tex`, `ce_o1_route.tex`, `ce_o1_global_transfer.tex`, `ce_o1_pre_edge.tex`, `ce_physical_log_far.tex`, `ce_rate.tex`). Lean: `ConvSource*`, `CeLift*`, `CeHbLiftAssembly`, `CeHankelPairFromEigen`, `EuclidCELift`, `CohnElkies/{MellinMainKernel,PhysicalAndFarTransfer,PreEdgeCriterion,LobeSaddle*,SaddleGeometry,OriginMellinAndS0,AiryGaussianTransform}` (about 20k lines).

| label | state | Lean today / note |
|---|---|---|
| `thm:ce-hb-lift` | partial | reduces to the open `CeHankelPair` at `m_0 = 1` (`ce_hb_lift_airy_of_hankelPair`); `CeHbLift` is stated for strict Laplace positivity only; weak positivity with tangencies and `m_0 > 1`: M8 |
| `lem:ce-dual-line` | planned | M6; no declaration (the hypotheses are the fields of `PreEdgeGeneralData`, `preEdge_general_pos`) |
| `lem:ce-lift-assembly` | partial | `ceAdmissible_of_hankelPair` (`EuclidCELift`), `CeHbLiftAssembly`; `ceLift_pair`, `ceHankelPair_of_eigenfns`, `ceLift_tune` |
| `cegt:GT2b` | done | `gt2b_reflected_combined`, `twoScaleS_gt2b_reflected_mult`, `o2_reflected_line_deriv_bound` |
| `thm:ce-post-edge` | planned | M6, open step (b) (Fourier sign `f_- <= f_+`); GT.3b `gt3b_far_fourier_transfer` and `preEdge_general_pos` exist as ingredients |
| `cepe:general` | partial | `preEdge_general_pos` on the hypothesis structure `PreEdgeGeneralData` (toy witnesses only; not instantiated for `D_c`) |
| `cepe:abs-saddle` | planned | M6; no declaration |
| `ceo:gauss` | done | `airySquare_gaussian_transform` |
| `ceo:conv` | partial | `ConvSource*`: `convS_bounds`, `convSource_mass`, `ConvTailData`, `HasU2` (O.12(1)-(3), (4) weight); O.12(5)-(7) on `Re z = 0` open (tail, dual, `O6DualEst`) |
| `ceo:O11ae` | done | `MellinMainKernel` (`bsplineMult`, `mainEdgeAmp`, `norm_mainEdgeAmp_le`) |
| `cepf:FG3` | done | `Tc_sup_bound`, `fourier_L1_le_sqrt_mul_H1`, `mainTransferOp_sup_norm_le` |
| `cepf:PF3` | done | `pf3_kernel_bound`, `pf3_kernel_bound_uniform` |
| `cel:L3a` | done | `OriginMellinAndS0` |
| `cel:L4` | done | `SaddleGeometry` (items (2), (3) as in the TeX) |
| `cel:L5` | done | `lobe_saddle_asymptotic`, `lobe_core_error_bound` |
| `cel:L7` | done | `integral_cos_sq_ge` (`SaddleGeometry`) |

**D2. Cohn-Elkies radius layer: finite dimensions, Schwartz vs `L^1` infimum, density** (`ce_finite_bounds.tex`, `ce_radius.tex`). Lean: `CohnElkies/{FiniteDimensionCrossings,FiniteGaussianBase,CohnElkiesRadius}`.

| label | state | Lean today / note |
|---|---|---|
| `thm:ce-gaussian` | done | `ce_quadratic_dimensions` (`FiniteDimensionCrossings`, `FiniteGaussianBase`) |
| `lem:ce-schwartz` | partial | the `X = empty` case: `ce_schwartz_radius_eq_L1_radius`, `ce_schwartz_bound_eq_optimalCohnElkiesBound`; strict signs at a finite shell set `X` are not stated |
| `gt:7.10` | not planned | owner-deferred; not on any headline path (the packing bound for integrable CE pairs) |
| `cor:ce-schwartz-shells` | planned | M9 (needs the sequence proofs of `thm:ce-airy-transfer`) |
| `gt:7.12a` | partial | `thm_intro_radii_ce`: `c_1 <= vol <= c_2` and the log law up to `O(1)`; the exact five-term density `eq:ce-density-exact` needs M10 |

**E1. Cohn-Elkies shells: reduction, extraction, one-profile, odd families** (`ce_shells.tex`). Lean: `ShellGap*` (about 2.7k lines), `ShellLaplaceBase`, `ShellLaplaceZeros`, `OddShellFamily`, `CEShellReduction`, `OneProfileEnvelope`, `HeadlineDefs`.

| label | state | Lean today / note |
|---|---|---|
| `thm:ce-shell-reduction` | partial | `shell_reduction_airy`, `shell_reduction_m1_proved` (`m = 1`); the general `ShellReduction D` is the open field of `ShellGapInputs`: M8 |
| `thm:ce-physical-profile` | partial | extraction form `hankelShellGapLimit_proved` (mass ratio, tails, Laplace limit, transport, Mellin reflection); the origin-floor clause and the endpoint case `u_* = t_m` are not stated |
| `par:ce-one-profile` | done | `one_profile_feasible_iff`, `one_profile_threshold_le_and_endpoint_iff`, `one_profile_maximizer_exists` (with `AiryCompactnessModel`, built from `one_profile_envelope`) |
| `thm:ce-shell-gap` | done | `hankelShellGapLimit_proved`, `shellGapLimit_of_hankel`; `thm_intro_gap_ii`, `thm_intro_gap_ii_even` (the statement carries an unused `ShellGapInputs` argument) |
| `cor:ce-projection-mass` | done | inside `hankelShellGapLimit_proved` (the constraint system `eq:ce-laplace-constraint`); no separate statement |
| `thm:ce-odd-family` | partial | `ce_odd_family_laplace_gap`, `odd_shell_family_laplace_gap` (Laplace-negative odd families); the Laplace-positive odd families (attainment at every odd `m`) are not stated: M8 |
| `thm:ce-laplace-zeros` | partial | `laplace_zero_multiplicity_le`, `laplace_zero_analyticOrder_le`, `laplace_pos_near_zero`, `laplace_pos_large_of_odd`, `laplace_m3_classification`; endpoint clause not audited |

**E2. Limiting Airy program at prescribed shells (Airy-LP)** (`ce_airy_lp.tex`, `ce_airy_lp_proofs.tex`, `ce_canonical_iff.tex`, `ce_two_level.tex`, `ce_shifted_witnesses.tex`, `airy_extremal.tex`). Lean: none (inputs in Lean: `airyNC_quadrature`, `hb_uniqueness`, `one_profile_*`, `hankelShellGapLimit_proved`, `airyAiC_logDeriv_mittagLeffler`, Clark two-node `AiryCft2Clark`).

| label | state | Lean today / note |
|---|---|---|
| `lem:qual-compact` | planned | M9/M8 (S lemma shared with the fold-tip blow-up `ft:L2`); not in Lean; check `SignUncertainty/` before adding |
| `thm:airy-square-attained` | planned | M9: statement in `ce_airy_lp.tex`; proof in `ce_airy_lp_proofs.tex` |
| `thm:ce-airy-transfer` | planned | M9: parts (1) two-sided bound, (2) exact coefficient, (3) stability, (4) uniformity on compacts |
| `lem:al-seeds` | planned | M9 |
| `lem:al-smooth` | planned | M9 |
| `lem:al-reference-positive` | planned | M9 |
| `lem:airy-shell-buffer` | planned | M9 |
| `lem:airy-active-height` | planned | M9 |
| `lem:airy-square-bound` | planned | M9: uses `airyNC_quadrature` and Mittag-Leffler `airyAiC_logDeriv_mittagLeffler` (both in Lean) |
| `lem:al-kernel` | planned | M9 |
| `prop:airy-secular` | planned | M9 |
| `lem:airy-node-square` | planned | M9 |
| `thm:airy-node-sign` | planned | M9 |
| `lem:al-hermite-approx` | planned | M9 |
| `lem:al-far-cardinal-laplace` | planned | M9 |
| `thm:al-rational-density` | planned | M9 |
| `(unlabelled) ce_airy_lp_proofs.tex:719` | planned | M9 |
| `lem:deflation-identity` | planned | M9 |
| `lem:ce-terminal-deflation` | planned | M9 |
| `thm:ce-canonical-iff` | planned | M9: (1)-(2), aliases `prop:airy-strictification`, `lem:airy-last-gap` |
| `thm:ce-shifted-lift` | planned | M9: the CE lift of strict shifted rational-Airy witnesses (route-II machinery at shifted nodes) |
| `lem:ce-rayleigh-two-level` | planned | M9 |
| `cor:ce-rayleigh-bound` | planned | M9 |

**F1. Five-term lower bound for the Hankel thresholds** (`constant_terms_lower.tex`). Lean: none (inputs in Lean: `HankelLanger*`, `gt:7.4`, `radial_compactness`, `hankel_quantC1_of_feasible`, `hankelBootHB`).

| label | state | Lean today / note |
|---|---|---|
| `ct:outer` | planned | M10 (lower bound) |
| `ct:dual-id` | planned | M10 (lower bound) |
| `ct:cfu` | planned | M10 (lower bound) |
| `ct:dyadic` | planned | M10 (lower bound) |
| `ct:boas` | planned | M10 (lower bound) |

**F2. Five-term upper bound for the Hankel thresholds and the Cohn-Elkies radius** (`constant_terms_upper.tex`, `constant_terms_five.tex`). Lean: none (inputs in Lean: `U.2`-`O.5` at one level, `airySquare_gaussian_transform`, `lobe_saddle_asymptotic`, `exists_hankelEigenfn_lift`).

| label | state | Lean today / note |
|---|---|---|
| `fct:main-hankel` | planned | M10 (upper bound) |
| `fct:main-ce` | planned | M10 (upper bound) |
| `fct:comp-D` | planned | M10 (upper bound) |
| `fct:phikill` | planned | M10 (upper bound) |
| `fct:warp-asymp` | planned | M10 (upper bound) |
| `fct:splitting` | planned | M10 (upper bound) |
| `fct:bump-5` | planned | M10 (upper bound) |
| `fct:ce-band` | planned | M10 (upper bound) |
| `fct:ce-preedge` | planned | M10 (upper bound) |
| `uct:outer-growth` | planned | M10 (upper bound) |
| `uct:airy-trans` | planned | M10 (upper bound) |
| `uct:pos-floor` | planned | M10 (upper bound) |
| `uct:strip-split` | planned | M10 (upper bound) |
| `uct:bump-est` | planned | M10 (upper bound) |
| `uct:seed-asymp` | planned | M10 (upper bound) |
| `uct:gen-preedge` | planned | M10 (upper bound) |
| `uct:ce-band` | planned | M10 (upper bound) |

**F3. Five-term theorem `thm:ct-upper` (assembly and reductions)** (`general_theorems.tex`). Lean: reductions in Lean: `hankel_euclid_dictionary`, `intertwiner_feasible`, `ce_schwartz_radius_eq_L1_radius`, `ce_quadratic_dimensions`, `hankelT0_eq_hankelT`.

| label | state | Lean today / note |
|---|---|---|
| `thm:ct-upper` | partial | (iii) (all `d >= 2`, Airy order, `O(1)`) is the Lean `thm_intro_radii` shape, conditional on `RadiiInputs` (open `ce_hb_lift_m1`); (i), (ii) five-term bounds: M10 |

**G. Fold-tip universality (Theorem FT and the two-edge versions)** (`fold_tip_universality.tex`, `fold_tip_two_edge.tex`, `fold_tip_two_edge_hb.tex`). Lean: `ModularBootstrap/FoldTip/*` (about 2.3k lines); `TwoEdgeBootstrap/FoldTipSeed`.

| label | state | Lean today / note |
|---|---|---|
| `fto1:sub` | partial | `ft_sub`, `ft_sub_displacement`, `ft_sub_feedback` (same hypothesis) |
| `fto1:thm` | partial | `ft_twoEdge_lower`, `ft_twoEdge_expansion`, `ft_twoEdge_lower_hb`: over the abstract two-edge bootstrap, the violator family as a hypothesis |
| `fto1:mellin` | planned | FoldTip lane (FT-7 with TL6) |
| `ft:FT` | partial | FoldTip lane: hypotheses H1-H4b as structures; conclusions for Paper II instances `ft_fixedWeight_general`, `ft_fixedWeight`, `ft_virasoro`, `ft_n1`; the Lean `FTH4b` does not match the paper (FT-H4b first FT target) |
| `ft:L1` | planned | FoldTip lane, FT-3..6 (after `ChartCompactness`) |
| `ft:L2` | planned | FoldTip lane, FT-3..6 (uses `lem:qual-compact`) |
| `ft:riesz` | planned | FoldTip lane, FT-3..6 |
| `ft:WP` | planned | FoldTip lane, FT-H4b |
| `ft:WR` | planned | FoldTip lane, FT-H4b |

**H. Introduction theorems** (`sign_uncertainty_core.tex`). Lean: `SignUncertainty/Headlines.lean` (`thm_intro_radii`, `thm_intro_gap_i`-`_iii`); the retired separation bound is in `SignSeparationLimsup.lean`.

| label | state | Lean today / note |
|---|---|---|
| `thm:intro-radii` | partial | Lean `thm_intro_radii`/`_sign`/`_ce`: the `O(1)` Airy-order radii and the density up to constants (shape of `thm:ct-upper` (iii) and `gt:7.12a`), conditional on `RadiiInputs`; the five-term statement is not stated |
| `thm:intro-hb` | planned | M8; no Lean statement (`HbThresholdsLower`, `HbThresholdsUpper` are the one-level halves) |
| `thm:intro-gap` | partial | `thm_intro_gap_i`, `_ii`, `_ii_even`, `_iii` (conditional on `ShellGapInputs`; (ii) does not use it); (iii) only for strict Laplace positivity; (iv) not stated: M9 |

### 6.3 Remarks that state something

Remarks are not counted above. The ones that carry content: `thm:ce-neumann` (Remark H.14c, the Neumann shell: recorded without proof in the paper, nothing depends on it; **not planned**); `rem:airy-even-deep-gap` (explicit data with `t_{m+k} < u_sh <= u_LP < t_{m+k-1}`, a remark with proof, small; planned with M9); `prop:odd-shell-certificate` (Remark: explicit odd-level instance by an exact-ball certificate; **not planned**: `ce_odd_family_laplace_gap` covers existence); `mat:T6` (symbol bounds for rational Airy functions: used through `Gt1NegTailAmp`, in Lean in the form `gt1BasisInput` needs); `uct:quintic-barrier`, `uct:rem-var`, `fct:rem-mech`, `fct:rem-num`, `ct:rem-split`, `ct:rem-lattices` (explanatory or numerical cross-checks: **not planned**; a finite-`c` numerical check is numerical evidence, never a Lean statement).

