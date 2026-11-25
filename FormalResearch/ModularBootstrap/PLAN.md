# Paper II (modular bootstrap at large c) — Lean plan

Source: QIprojects `CFT/modular_bootstrap/paper/` at `origin/main` `f4cc9812c` (`airy_scale_core.tex` and its supplement parts; the
note `CFT/notes/n2_ramped_comb.tex` for Lemma U*). Lean state: reasoner `master` `5b7fa76`. Reader-facing status line:
the Paper II section of QIprojects `docs/lean_status.md`. This file says what is true now: nothing is claimed formalised that
is not on `master`, and a `.lean` file existing is not verification.

**Where things stand in three sentences.** The lower side is Lean-checked at every integer `(w,Q)` of `(H_w)`; the upper side
reaches the `O(1)` two-sided law only for weight one (every product `Q`, including `N = 1`), with the bump for `w > 1` half
built; the two-level curve and its fold-tip instances are done at weight one and conditional on named inputs above it.
The five-term expansion, primal attainment, the infinite-order derivative limit, integrality, positive mixtures and all spin
results are not in Lean; sections 1 to 3 give each a place in a priority and dependency order. Under `FormalResearch/` there is no proof placeholder and no
`axiom` declaration, and the headline theorems named below carry `#print axioms` guards with `[propext, Classical.choice, Quot.sound]`.

**Counts.** The paper and supplement state 249 results (246 `result` environments, the two `theorem`/`corollary` of
`modular_bootstrap_gap_proof.tex`, and Lemma A$_V$, which is a `remarkx`; several labels on one result are one row). Their state
on `master`: 72 done, 24 partial (Lean covers a special case, stated in the row), 125 planned (a named
work package), 6 not planned (with the reason), and 22 recalled from Paper I (mapped in 7.10, not Paper II packages).
Of the 22 recalled results, 15 are formalised in Lean (in Paper I's files or in this lane's), 1 is partial (`teb:quant_c1_hb`) and
6 are not formalised (`ap:lemH`, `ap:lemFR`, `ap:lemHp`, which no Lean route here needs; `sr:window-pairing`, `sr:WR`, `teb:quant_c1_near`, which are owned by FT-H4b and FIVE-L).

## 0. Vocabulary (read before section 1)

- **State.** *done*: the paper's statement, in the paper's scope, is a Lean theorem with pinned axioms. *partial*: Lean proves
  a special case (Virasoro, integer `w`, `w = 1`, two-level `F = {t_1}`, ...) or part of the statement, or proves it modulo a
  named hypothesis; the row says which. *planned*: a work package of section 4 owns it. *not planned*: reason given.
- **Proved modulo X**: the theorem has hypothesis X (a structure or `Prop`) that is not itself proved on `master`.
  **Stated**: a definition or statement exists without proof of the theorem. These words are used in that sense only.
- **Size** (lines of Lean): S < 500, M 500-2000, L > 2000. Calibration from `wc -l` is in Appendix B; for planned packages the
  size is an estimate from the closest finished directory.
- **`(H_w)`**: integer weight `w >= 1`, null factor `Q = prod (1 - q^{mu_l})`, `mu_l > 0` (Lean: `FixedWeightProblem`);
  `(H_{w,mix})`: positive finite mixtures of shifted products (no Lean structure yet).

## 1. Priority order: the four headline results

The introduction of `airy_scale_core.tex` states four results. Work is ordered by what each needs; packages off every headline path
are in tier 2 (section 3). "Lean statement" says whether the Lean theorem is the paper's statement or weaker (a special case, a
weaker remainder, or modulo a named hypothesis). Package definitions, sizes and dependencies are in section 2.

| # | headline (paper) | Lean statement today and how it compares | ordered package path from master |
|---|---|---|---|
| **3** | **Five-term expansion** `thm:fixed-weight-expansion`, `thm:spinless-expansion`: `Delta_best = c'/Lambda_V + A_opt c'^{1/3} + c_0^* + c_1^Langer c'^{-1/3} + d_2^* c'^{-2/3} + O(c'^{-1} log c')`, two-sided | **Weaker.** `Upper.Ramped.virasoro_corollary_E1_unconditional` (Virasoro) and `n1_corollary_E1_unconditional`: `Delta_best = c'/Lambda_V + A_opt c'^{1/3} + O(1)`, two-sided, every weight-one problem; lower half `O(1)` at every `(w,Q)` (`fixedWeightLowerBoundInput_of_problem`). No `c_0^*`, `c_1^Langer`, `d_2^*` in Lean; for `w > 1` the upper half is the hypothesis `TheoremC15UpperInput` | Virasoro: **FIVE-0**, then **FIVE-L** and **FIVE-U** in parallel (they give `cts:transfer` and `thm:spinless-expansion`). Every `(w,Q)`: **W-P5**, **W-P6** (bump, `O(1)` upper bound at `w > 1`), then **FIVE-W** |
| **2** | **Extremal spectrum**: attainment and atomicity (`ds:primal`), Airy clusters (`sr:Sigma`, `sr:cor`, `sr:single-level`), Clark curve (`gt:2.1`, `gt:2.4`-`gt:2.6`) | **Weaker or special.** `Sigma_0`, `Sigma`: `virasoro_sigma_unconditional`, `sigma_unconditional_prob` for the extremal measures of weight-one problems (paper: any measure satisfying `Gap`; far-first-site omitted family). Clark curve: `concrete_two_level_theorem` (`gt:2.1`, every `(w,Q)`, tests) matches; `theorem_two_five_w1`, `theorem_two_six_w1_unconditional` (`gt:2.5`, `gt:2.6`) weight one only. Existence of an exact-gap crossing measure (`corollary_E1`), not atomic: weaker than `ds:primal`. Nothing for `sr:cor`, `sr:single-level` | **DU-G**, **PA1** (`ds:primal`); **W-P5** (`Sigma`, T2 inputs at all weights), **SR-COR**; **W-P6**, **W-T2w**, **SE3** (Clark boundary at `w > 1`); **SLK**, then **PA2** (`sr:single-level`; the exact first atom needs `c_0^*` of FIVE-W) |
| **4** | **Universality across chiral algebras**: fixed weight (`n1:T5`) and `N = 1` (`n1:T3`), positive mixtures (`pmix:main`), prescribed HB levels | **Partly the paper's.** Lower bound `O(1)` at every integer `(w,Q)` and `N = 1` matches `wone:genlower`(1); `O(1)` law at weight one. Two-level duality `ds:E`(a) at `F = {t_1}` for every `(w,Q)` (`constrained_strong_duality_two_level`) and `gt:2.4` at `w = 1` (`corollary_two_four`); `ds:E`(b) (`T_F = max`) only at `F = empty` (`theorem_E`). Five-term, general compact `F`, mixtures, general HB levels: none | five-term at `(w,Q)` as in 3 (this covers `N = 1`); mixtures **PM-0**, **PM-1** (= W-P6 for one component), **PM-2**, **PM-4**; then **PM-3** (`pmix:rigidity`, needs PA2, W-T2w, SLK, FT-H4b), **INT-2HB** (cites `pmix:rigidity`), and **PM-5** (`pmix:main` cites `int:hb-reserve`, `int:main`, `int:obstr`, `ctu:c0`); `gt:hb` (**HB1**) is the single-component case of `pmix:rigidity` plus `int:hb-reserve` |
| **1** | **Spin does not help**: continuous spin (`s4:S4`, `spinnotes:S3`, `sd:R`), integer spin (`isl:main`), finite-order programmes (`isl:finite`); integrality shifts the spinless optimum exponentially little (`int:main`) and by `O(log c')` with continuous spin (`int:cont-spin`) | **None.** Only the spinless upper bound (`O(1)` form) that the spin results compare with exists | continuous spin: **SPIN-F**, **SPIN-D** (its `sd:LP` needs **LP1**, which needs DU-G), **SPIN-S4**. Integrality: **INT-T**, **INT-1**, then **INT-3** (needs INT-2 and W-P6), then **INT-S** (needs SPIN-S4, SPIN-D, INT-1, INT-4, FIVE-U's `cts:transfer`). Integer spin and finite-order programmes: **SPIN-Z** last (the Arb enclosures as the named hypothesis `SpinZEnclosures`, owner decision; certificates later). Lattice integrality is not planned ((CLM)-conditional, INT-L) |

The rows are ordered by the length of the critical path, longest first, not by the paper's numbering; "#" is the paper's number.
Common infrastructure on several paths: W-P5 (all weights, headlines 2, 3, 4), W-P6 (the `O(1)` upper bound for `w > 1`: headlines 2, 3, 4),
DU-G (headlines 1, 2).

**Next package to start: FIVE-0** (headline 3, the longest chain, no open parent): the closed-form constants `c0Star`, `c1Langer`, `gamma0`,
`d2Star`, the Langer curvature and phase-locking identity (`cts:langer`, `cts:phaselock`), then the outer function on the half-disc and the exact
minimum of `J` (`cts:involution`, `cts:main`). First risk to settle: Mathlib has no outer functions or Hardy spaces on the half-disc, so build it
from the Poisson integral of the log modulus, with `rmt-foundations-lean`'s Cayley/Herglotz file and `Complex/HardyHalfPlane` (section 2.2). Started alongside it, on the
same headline paths: **W-P5** (mechanical, P1-P4 done) and then **W-P6**; **DU-G** and **SPIN-F** have no open parent.

Note on the owner's earlier ranking (1. Theorem LP, 2. INT-4 then INT-1 to INT-3): all of these are now tier 1 on headline paths (LP1 for
SPIN-D and HB1; INT-T, INT-1, INT-3, INT-4 for headline 1's integrality clause), ordered by their dependencies (section 2.1).

## 2. Tier 1: work packages on a headline path

Sizes are estimates (S/M/L as in section 0). "Closes" lists labels whose state changes. Packages closed by an earlier row
are named in "needs". Calibration: the weight-`w` lower bound (`FixedWeightBand`) took 19k lines, the weight-one `O(1)`
upper bound (`Upper/Ramped`) 19k, T2 (`TwoZero*`) 5.6k, the whole Virasoro lower half about 29k.

**Tier 1a: on the direct paths of section 1.**

| WP | content | closes | needs | size | wave |
|---|---|---|---|---|---|
| **FIVE-0** | constants and exact minimisation: `cts:langer` (Langer curvature, `K_2`), `cts:phaselock`, `cts:involution`, `cts:main` (closed-form minimum of the convex functional `J`, `c_0^*`), outer-function jets `ctu:piece4`, `ctu:jets`, `ctu:common-functional`. New definitions `c0Star`, `c1Langer`, `gamma0`, `d2Star` by their closed forms (decimals are numerical, not planned). Risk: Mathlib has no outer functions or Hardy spaces on the half-disc; `Complex/Hardy{HalfPlane,FejerRiesz,Point}` is the nearest infrastructure, and the outer function would be built explicitly from the Poisson integral of the log modulus | the seven labels | none | L, 8-12k | wave 1 |
| **FIVE-L** | sharp lower bound: `cts:edge-hankel`, `cts:cauchy-dual`, `cts:rosc-uncond`, `cts:boas`, `cts:lower-main`, `ctl:dyadic`, `ctl:pass2`, `ctl:freeze`; inputs `rem:corL` (packaged `C^1` stability and envelope), `rem:thmOloc` (Airy translates satisfy the local conditions), `teb:quant_c1_near` (TE.0 flat, near-threshold: new file beside `QuantC1Airy`, which Paper I imports and is not edited) | those, `rem:corL`, `rem:thmOloc` | FIVE-0, STAB, `theoremJ_Delta_best`, `theorem_W1prime_two`, `teb_quant_c1_typeII` | L, 25-30k | wave 2 |
| **FIVE-U** | sharp upper bound by the exact comb with smoothing: `cts:smooth-env`, `cts:tip-shared`, `cts:upper-design`, `cts:regionII-floor`, `cts:shifted-langer`, `pm:tip-match`, `cts:upper-vac`, `cts:transfer` (C15 at Virasoro), `thm:spinless-expansion` | those | FIVE-0; `esd:*`, `cmb:K1`, `K4`, `K7`, `ut:G`, `fw:FWM` (all done) | L, 25k | wave 2 |
| **FIVE-W** | fixed weight: `ctu:main`, `ctu:O1` (`c_0^*(w,Q)` clauses), `ctu:table` (closed forms), `ctu:weight`, `ctu:strip`, `thm:fixed-weight-expansion` | those | FIVE-L, FIVE-U, W-P5, W-P6, `fixedWeightAxioms_of_problem` | L: 5-8k if FIVE-0/L/U are stated over `FixedWeightProblem` from the start (recommended), 15-25k if they are Virasoro-only and duplicated | wave 3 |
| **W-P5** | design side at every weight: Proposition V and Lemma T with the bump (Peano bound `fw:e3.6`), Property (P) for the bumped `f = 1` designs, `Sigma_0`, `Sigma`, hypotheses H3, H4a, H4b of `ft_fixedWeight` at every `w` (mostly mechanical, P1-P4 done) | `ut:Vac`, `ut:T`, `sr:P`, `sr:Sigma0`, `sr:Sigma` at every weight; `wone:clark`(a) | P1-P4 (done), `Upper/Rigidity` | M-L, 4k | wave 1 |
| **W-P6** | `O(1)` upper bound at every `(w,Q)`: bumped ramped comb (Lemma U*(w), `fw:Ustar` in `n2_ramped_comb.tex`; the paper label is `pmix:ramped` at one component), ramped vacuum at `w > 1` (`theta_bound` in `RampedVacuumWindow`), giving `TheoremC15UpperInput prob` for every `prob` | `ctu:O1` first inequality, `ds:E1`, `gt:2.4`(a) at `w > 1` | W-P5 (Proposition V at weight `w`), P1-P4 | L, 8-12k | wave 2 |
| **W-T2w** | T2 `ut:T2` and ideal windows `ut:ideal` at `w > 1` and general `m`, Remark T2.1 (more real zeros), Theorems 2.5, 2.6 at `w > 1`, `ut:IIF`, `ut:I`, `ut:III` for finite real factors; `TwoZero*` pieces that say `prob.w = 1` (`Positivity/RegionOne*`, `Vacuum*`, `Assembly/Psi*`) generalised in place | `ut:T2`, `ut:ideal`, `ut:IIF`, `wone:clark`, `gt:2.4`-`gt:2.6` at `w > 1` | W-P5, W-P6 | L, 5-8k (the `w = 1`, two-factor `TwoZero*` alone is 5.6k) | wave 3 |
| **SE3** | `se:3.3` at every `(w,Q)`: crossing measure supported in `{t_1} union [T, inf)` with mass at `t_1`, `T <= T_* + A_2^* n^{1/3} - D_J`; model `wone_clark_two_level_boundary` and `corollary_two_four_of_upper` (the upper bound gives the mass at `t_1`) | `se:3.3` | W-P6, `theorem_W1prime_two`, `constrained_strong_duality_two_level` (done) | S | wave 3 |
| **DU-G** | `ds:E` as stated: (a) arbitrary closed `X` (existence iff no feasible test, at most card `B` + 1 atoms, decreasing supports), (b) compact `F`, `T_F = max`, `nu(F) > 0` above `T_V`, (c) reserve separation; `ds:farkas` in its stated form | `ds:farkas`, `ds:E` | `Duality/`, `FixedWeight/StrongDuality`, `TwoLevel/ConstrainedDuality` | M, 1.5k | wave 1 |
| **PA1** | `dsl:strip-fixed` (fixed-charge strip bound `n1:L4`(a), positive weak threshold), `ds:primal` (weak extremal `g_*`, support in `{g_* = 0}`, locally finite atomic, atom at `T_F`; Montel/limit of `g_j` and `L^1(t^{w-1}dt)` convergence) | `dsl:strip-fixed`, `ds:primal`; atomic part of `ds:E1` | DU-G, `FixedWeightBand/MellinW`, `WeightAxioms` | L, 3-4k | wave 2 |
| **SR-COR** | `sr:cor`: positions and masses of the clusters of a near-extremal measure in `t` | `sr:cor` | `Sigma` (weight one done), the spectral-measure dictionary (`Upper/Rigidity/CrossingDictionary`) | S-M | wave 1 |
| **PA2** | `dsl:one-level-clusters`, `dsl:near-opt-mass`, `sr:single-level`; the cluster structure needs only the `O(1)` law, the exact first atom `d_1` and `(t_2^* - t_1^*) c^{-1/3}` need `c_0^*` | those three | PA1, W-P5, FIVE-W (it uses `rig:R`, not `bl:norm`) (`ctu:c0`) | L | wave 4 |
| **SLK** | `bl:norm`: shared Airy/HB normalisation and `L^1` convergence with vacuum slack, first for `m_0 = 1, 2` (Airy, Clark), then general `m_0` with HB1 | `bl:norm` | `Blowup/`, `hb_uniqueness`, `ft:PP` (done) | M, 1.5k | wave 1 |
| **LP1** | `ds:cay` (Cayley identity), `ds:cont` (positive-Laplace continuation), `ds:mom` (Laguerre moment growth), `dsl:poly-compact` (shared polynomial moment compactness), `ds:LP` (i)-(iii). `dsl:poly-compact` is also the engine of `sd:LP`. Since QIprojects PR 292 it is proved by one positive extension: coercive majorants `h_N`, the sublinear functional `p(f) = inf{L(v) : v >= f}` on continuous functions of polynomial growth, a real Hahn-Banach extension (Mathlib `exists_extension_of_le_sublinear`), the Riesz-Markov representation on `C_c(X)`, and a cutoff argument; there is no sequence of truncated measures and no weak-`*` limit. `dsl:positive-ray` (`ds:LP` (iii)) is an instance of it | `ds:LP`, `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact` | none beyond Mathlib (Hahn-Banach, Riesz-Markov) and `ds:mom`; `Duality/Farkas` is only an alternative for the truncated form | M-L, about 3k | wave 2 |
| **SPIN-F** | continuous spin foundations: `spinnotes:S1` (formulation, certification), `S21`, `S22`, `S22b`, `S23`, `S24`, `S3` (slope `-C c^{1/3} (log c)^{2/3}`), calibration `scal:C1`, `scal:C3` | those nine | `Crossing/` (Mehler, Hermite), `Chart/` | L, 15-20k | wave 1 |
| **SPIN-D** | `sd:M`, `sd:T`, `sd:P`, `sd:SD`, `sd:W`, `sd:V`, `sd:A`, `sd:LP`, `sd:R` | those nine | SPIN-F, LP1 (`sd:LP`), DU-G | L | wave 3 |
| **SPIN-S4** | the sharp Airy coefficient with spin, `-O(log c')`: `s4:S4`, `s4:2.1` to `s4:6.1`, `s4:4.4` | the fourteen `s4:*` | SPIN-F, SPIN-D | L, 25k+ | wave 4 |
| **PM-0** | mixtures, interface: `pmix:rebase`, `pmix:weight` (W1-W4), `pmix:crossing`, `pmix:jets`. Design suggestion: generalise `FixedWeightProblem` to a finite exponential-sum amplitude `A(x) = sum c_r e^{-4 pi r x}` (`ctu:jets` now treats any real-analytic amplitude bounded above and below on `[xi_*, oo)`, with bounded derivative, and the Cardy expansion `ctu:V-exp-A` holds for any finite signed measure of shifts, so dominated sources are covered; since PR 292 `pmix:jets` also carries the tip-weighted Jensen comparison `j(w,A) >= sum_i p_i (c_0^*(w,Q_i) - 12 xi_bar r_i)` with its equality criterion, using the shift integral `int_0^oo x'(t)/t dt = xi_*/sqrt 2`; products and mixtures are instances), so the lower chain is re-run rather than rewritten; the alternative is an abstract axioms structure (also gives real `w`). This is the main risk of the mixture lane | four labels | `WeightAxioms/`, `Crossing/Setup` | L (refactor) | wave 1 |
| **PM-1** | `pmix:punif`, `pmix:ramped`, `pmix:smooth`, `pmix:o1`; the single-component case of `pmix:ramped`, `pmix:o1` is W-P6 | four labels | PM-0, W-P6 | M-L | wave 3 |
| **PM-2** | `pmix:vac` (fixed-design transfer for mixtures) | `pmix:vac` | PM-0, PM-1, W-P5 | M | wave 4 |
| **PM-4** | `pmix:duality`: direct instance of `ds:M`, `ds:E`, `ds:primal`, `ds:LP` for mixtures | `pmix:duality` | PM-0, DU-G, PA1, LP1 | S-M | wave 3 |

**Tier 1b: the HB level (`pmix:rigidity`, `int:hb-reserve`, `gt:hb`, `pmix:main`).** In the TeX the order is PM-3 (`pmix:rigidity`) -> INT-2HB (`int:hb-reserve`) -> HB1 (`gt:hb`) and PM-5 (`pmix:main`).

| WP | content | closes | needs | size | wave |
|---|---|---|---|---|---|
| **FT-H4b** | realign `FTH4b` to the paper's H4b (`ft:H4b`; checked against `fold_tip_universality.tex`): general Hermite-Biehler data `(P,Q)`, terminal index `m`, support clause (a), one-sided designs (D1)-(D4); then Lemma WP (`sr:window-pairing`), Lemma WR (`sr:WR`) and C5(c) at every HB level (`FTSigma` is the Airy level at weight one only). The present `windows` field assumes tail bounds that are conclusions of WP, so it is replaced, not extended; Concordance row C5c is re-pointed | `sr:window-pairing`, `sr:WR` (recalled) | FT-1, `Upper/Rigidity` | M-L | wave 1 |
| **FT-CC** | the base structure `ChartCompactness` (`compactness_subseq` plus site and tail positivity, abstract setting; section 6), the core of FT-3 | `ChartCompactness` on master | none | M | wave 1 |
| **STAB** | stability slopes: `rem:thmBstab` (`I(delta)/delta -> 1/(2 L_*)`), `se:terminal-stability` (HB terminal node), `se:3.1` (two-level, `kappa_2(u_1)`) | the three labels | Paper I Theorem B equality (`airy_sign_equality_iff`), Clark equality (`clark_two_node_equality_iff`), `hb_uniqueness` (all done) | M, 1.5k | wave 1 |
| **INT-2** | `int:reserve` (linear reserve growth below the optimum, constant `kappa_res = 1/(2 ell_V L_*)`), `int:strict-weak` | the two labels | DU-G, STAB, W-P5 (`Sigma_0`(b) at every weight), W-P6, `bl:T`, SLK (`bl:norm` at `m_0 = 1`), Paper I Theorem B | M-L | wave 3 |
| **DU-F** | `se:cdual`: compact `F` constrained duality with attainment, atomic with a positive atom at `T_F` | `se:cdual` | DU-G, PA1 | S-M | wave 3 |
| **INT-2HB** | `int:hb-reserve`: prescribed-level HB reserve (any strict HB pair; `m_0 = 1` is `int:reserve`) | `int:hb-reserve` | INT-2, STAB, SLK, FT-H4b, PM-3 (`pmix:rigidity`), DU-F (`se:cdual`) | L | wave 6 |
| **HB1** | `gt:hb` for general `(P,Q)` (the paper proves it as the single-component case of `pmix:rigidity` with `int:hb-reserve`, `sr:single-level`); closes `wone:ftlfw`, `wone:genlower` for all `m_0`; Paper I's M8 (TE.0' for all `(P,Q)`, via `ChartCompactness`) is an input | `gt:hb`, `wone:ftlfw`, `wone:genlower` (general `m_0`) | PM-3, INT-2HB, PA2, FT-H4b, SLK, PA1, LP1, FT-CC, Paper I M8 | S-M after its inputs | wave 7 |
| **PM-3** | `pmix:hbphase`, `pmix:hbtap`, `pmix:rigidity`; `gt:2.1`, `gt:2.4`-`gt:2.6` for mixtures | those three | PM-1, PM-2 (`pmix:vac`), PM-4 (`pmix:duality`), PA2 (`dsl:one-level-clusters`, `dsl:near-opt-mass`), W-T2w (`ut:ideal`), SLK (`bl:norm`), FT-H4b (`sr:window-pairing`, `sr:WR`), W-P6 (`wone:ftlfw`) | L | wave 5 |
| **PM-5** | `pmix:main` (assembly) | `pmix:main` | PM-0 to PM-4, INT-2HB, INT-3, INT-4, FIVE-W (`ctu:c0`) | S | wave 7 |

**Tier 1c: the integrality clause of headline 1** (the introduction's first result states that integrality shifts the spinless optimum by an exponentially small amount, `int:main`, and with continuous spin by `O(log c')`, `int:cont-spin`).

| WP | content | closes | needs | size | wave |
|---|---|---|---|---|---|
| **INT-T** | elementary integrality tools: `int:int-closed` (vague closedness of integer counting measures), `int:cheb` (1D midpoint-cosine moment matching; exact in `N`, not a fixed-`N` check; since PR 292 its floor is `W_0 >= 640 N^2`, by the filtered right inverse on the oversampled grid `N' = 2N`, with the Fejer kernel norms `||V'||_1 <= 5 pi n/sqrt 3`, `||V''||_1 <= 3 pi n^2`, contraction on the cube `1/(16n)`), `int:cheb-explicit` (the Euclidean inverse and the floor `8 N^{5/2}`, now its own lemma), `int:repair-identity` (the generic projection identity for the radial and tensor-cosine repairs), `int:sonine`, `int:repair`, `int:shell-inv` | those labels | none | L, 5-8k (about 224 dense TeX lines at the observed 25-45x Lean/TeX ratio) | wave 1 |
| **INT-1** | `int:atom`: cell-by-cell atomisation of a reserved crossing measure; since PR 292 it takes an abstract floor function `W(M)` (any sufficient density floor; `640 (M+1)^2` by `int:cheb`) and a moment order `M_k >= K H_k / log P_k`, and the explicit-floor variants are gone from it and from `int:main` | `int:atom` | INT-T | M-L | wave 2 |
| **INT-3** | `int:main`: exponentially small integrality gap at every fixed weight | `int:main` | INT-1, INT-2, INT-T, W-P6 (the `O(1)` law); FIVE-W (`ctu:main`) and PA2 (`dsl:near-opt-mass`) for its five-term and first-cluster corollaries | M | wave 5 |
| **INT-S** | integrality with continuous spin: `int:axis-trace`, `int:cheb2d` (elementary, self-contained), `int:cos2d-repair`, `int:cont-spin`; also `int:obstr`(b) | those four | SPIN-S4 (`s4:S4`, `s4:eSlack`), SPIN-D (`sd:M`, `sd:SD`), DU-G (`ds:farkas`), INT-1 (`int:counting`), INT-4 (`int:obstr`), INT-T, FIVE-U (`cts:transfer`); not INT-3 | L | wave 5 |
| **INT-4** | `int:obstr`(a): the supremal integer gap is attained; `Delta^Z = Delta^R` iff some attaining real measure is integer-weighted (the "iff" needs PA1); (b), swap-invariant spin cones, is INT-S | `int:obstr` | INT-T (`int:int-closed`), DU-G, `fw:crossing`(1) (done); PA1 for the "iff" | M | wave 3 |
| **SPIN-Z** | integer spin on closed twist cones and finite-order programmes: `isl:main`, `isl:finite`, `spinnotes:K1`-`K4a`, `L0a`-`L9`. Computer-assisted in the paper (Arb enclosures for the small-`Delta` symbol `P_4` and 26 multiplier boxes). **Owner decision (2026-11-25): in Lean the enclosures are one named hypothesis structure `SpinZEnclosures` (each enclosed inequality stated exactly as the paper's Arb check asserts it, with its box), and SPIN-Z proves `isl:main`, `isl:finite` from it**; kernel-checked certificates (the former precedent `o4QuotientBound` has since been proved analytically and its box certificate removed, so the only kernel-certificate precedent left is the `QVCheck` `native_decide` chain, which is not acceptable here; use `decide +kernel` on exact rationals, or Mathlib's `dyadic_interval`) wait until the other headline work is done. **Per-item fields (after QIprojects PR 290; split the structure accordingly, one field per item, so each can be discharged on its own):** (1) the collar (`W = 0.037` and the `e_a` step), (2) the finite slit, (3) the slit tail, (4) the edge coefficients, (5) the edge saddle excess (`D_tot = D_s + D_e`, `D_s < 10.94`, `D_e < 3.73`, `D_tot < 14.67 < 20`), (6) the 26 intermediate boxes (the 37992-rectangle covering of the K.4 modulus is closed in `R556`), (7) the plain tip bound, plus the small-`Delta` symbol `P_4`. Items (1)-(4) and K.4a need only elementary-function enclosures; the first target is the real-collar `P_4` bounds, which need a Ball enclosure layer (Mathlib has none: reuse `ThirdParty/interval`). A smaller `c_quad` may be possible (unverified, `R557`). **Lean-friendly discharge routes (QIprojects PR 294, merged `2587d98`; claim class in `notes/K4_LEAN_PATH.md`: exact-rational or interval certificates of the numerical inputs plus an analytic transfer proved there, an alternative to and not a replacement of the paper's Arb inputs; `python-flint` is not needed for any of them):** (5) the complete exact-rational P4 edge with no Arb and no historical logs (`verify_spinning_integer_p4_edge_{outer,tail,full}.py`; `D_e < 4.759`, `D_tot < 15.70`, `c1_{P4} > 43.10` against the paper's `3.73`, `14.67`, `44.13`; the weaker constants still close Part L); Check 4 by one uniform unregularised `M4_pf` symbol (`verify_spinning_integer_pf_*.py`; edge `< 8.4`, slit `< 13.2`, minimum margin `1.05e-8`); (6) a seven-box Check 5 cover in place of the twenty (`CERT_POLY_LEGACY=0`; worst margin `-1.776e-4`; Part L accepts only the seven- or twenty-box cover) built on the global plain tip bound `f'' < -111` on `[0, 0.072]` (`verify_spinning_integer_plain_global.py`, item (7)); the single-anchor homotopies (`m1_homotopy`, `two_harmonic_homotopy`) are notes-level and not consumed by Part L. If the `SpinZEnclosures` fields are discharged with these routes, state the field with the constants of the route used and say so; the field as the paper states it (`D_e < 3.73`, twenty boxes) stays the default. Paper corrections of the same PR: K.2(2) (only the vanishing prefactor `G_1 b coth(pi b) - 2` of `g_{1,0}` is even) and L.4(b) (`S~_eff` uses the harmonic-subtracted nonnegative slit excess and is nondecreasing in `kappa~`). Corrected in PR 290: the `M_{e^{0.5}}` modulus bound on `main` was false and the signed version is what K.4(1) needs; the K.3 hypothesis was unproved beyond `0.015`; the claim classes of `notes/K4_LEAN_PATH.md` mark which items are exact-rational verifier output, not Lean | `SpinZEnclosures` | SPIN-S4, SPIN-D | M (analytic part; certificates later) | wave 5 |

### 2.1 Order and waves for tier 1

Edges (a package waits for everything it needs; checked against the `\ref`s of each proof in the TeX, 2026-11-25):

```
FIVE-0 -> FIVE-L, FIVE-U -> FIVE-W <- W-P5, W-P6                          [headline 3]
W-P5 -> W-P6 -> {SE3, W-T2w, FIVE-W, PM-1, INT-2}                          [headlines 2, 3, 4]
DU-G -> PA1 -> {INT-4, DU-F, PM-4} ; PA1 + W-P5 + FIVE-W -> PA2            [headline 2]
DU-G -> LP1 -> {SPIN-D, PM-4} ; SPIN-F + SPIN-D -> SPIN-S4 -> {SPIN-Z, INT-S}   [headline 1]
INT-T -> INT-1 ; INT-1 + INT-2 + FIVE-W + PA2 -> INT-3 ; INT-1 + INT-4 + SPIN-S4 + FIVE-U -> INT-S   [headline 1]
PM-0 -> PM-1 -> PM-2 ; PM-1 + PM-2 + PM-4 + PA2 + W-T2w + SLK + FT-H4b -> PM-3   [headline 4]
PM-3 + INT-2 + STAB + DU-F -> INT-2HB -> {HB1 (+ FT-CC, Paper I M8), PM-5 (+ INT-3, INT-4, FIVE-W)}   [headline 4, HB level]
```

| wave | packages | why |
|---|---|---|
| 1 | **FIVE-0**, **W-P5**, DU-G, SPIN-F, STAB, INT-T, FT-H4b, FT-CC, SLK, PM-0, SR-COR | no open parent |
| 2 | **W-P6**, PA1, FIVE-L, FIVE-U, LP1, INT-1 | need wave 1 only |
| 3 | W-T2w, SE3, FIVE-W, SPIN-D, PM-1, PM-4, INT-2, INT-4, DU-F | need waves 1-2 |
| 4 | PA2, PM-2, SPIN-S4 | |
| 5 | PM-3, INT-3, INT-S, SPIN-Z | SPIN-Z with the enclosures as the hypothesis `SpinZEnclosures` |
| 6 | INT-2HB | needs PM-3 |
| 7 | HB1, PM-5 | |

A wave lists packages whose inputs are all in earlier waves; it is an order, not a schedule (wave 1 has more packages than build slots).

There are no time boxes; a stalled route is a ledger row, not a stop. At most two Sonnet-high agents at once; launch while at least
1.5 GB of disk is free. Sonnet high for the L packages, Sonnet medium for S-M, Haiku for docs and `THEOREM_MAP.md` rows. For each long lane
(FIVE-*, SPIN-*, PM-*) five pushes adding results without moving the lane's headline force a direction statement in the PR state.

### 2.2 Existing code to reuse (searched 2026-11-25; declarations read in the source)

Inside reasoner (no porting):
- `Complex/Montel.lean` (`montel`, `montel_family`) and `Analysis/Scheffe.lean` (`tendsto_integral_norm_sub_of_tendsto_ae`): the normal-family and `L^1` steps of **PA1** (`ds:primal`), **SLK** and **SPIN-D**.
- `Upper/Rigidity/VagueLimit.lean` (`IsVagueLimit`, `exists_vagueLimit`, on `ℝ`) with `Duality/MeasureCompactness.lean` and `Duality/Farkas.lean`: generalised to closed `Y ⊆ ℝ^d`, this gives `int:int-closed` (**INT-T**); `dsl:poly-compact` (**LP1**) no longer uses them (see its row); `TwoLevel/ConstrainedDuality.lean` is the base of **DU-G**.
- `StripBand/StripPoissonRep.lean`, `Complex/StripPoisson.lean`, `Complex/HardyHalfPlane.lean`, `Analysis/VanDerCorput.lean`: strip Poisson representation and oscillatory bounds for **FIVE-L** and Paper I F1/F2.

External (Apache-2.0 unless noted):
- **`rmt-foundations-lean`** (github.com/chenle02/rmt-foundations-lean; Lean v4.35.0 and Mathlib v4.35.0, one release behind reasoner's pin v4.36.0 since the 2026-11-25 bump, so it needs porting (the `Matrix.mul_apply`/`one_apply` shadowing, `Function.swap` in matrix `simp` sets and the `Nat.strong_induction_on` case name `ind` are the likely breakages; see the Lean skill's `references/mathlib-bump.md`); no proof placeholders): `RMTFoundations/Measure/HerglotzBorel.lean` (`cay`, `invcay`, `cay_mem_upper`, `poisson_cayley`, `disk_herglotz`, `herglotzBorel`) and `Measure/StieltjesInversion.lean`. Vendor under `ThirdParty/` for the half-disc to half-plane Schwarz/Poisson construction of **FIVE-0** (`cts:involution`) and for `ds:cay`, `ds:cont` in **LP1**.
- `PrimeNumberTheoremAnd` (Lean v4.36.0): rectangle contour shifts (`ResidueCalcOnRectangles.lean`) and `norm_fourier_le_integral_deriv_div`; port selectively.
- `HardySpace_formalization` has a disc `outerFunction` with boundary values, but no licence file and targets Lean v4.36.0-rc1: reference only.
- Nothing found for two-variable `(h, hbar)` modular kernels (SPIN-*), `int:cheb`, `int:sonine`, `ds:mom`.
- Newer Mathlib (after reasoner's pin): Poisson-Jensen (#42475), `besselJ` derivative recurrences (#42825, #43853), the `dyadic_interval` tactic (#45427 and follow-ups; an alternative for SPIN-Z certificates, alongside the exact-rational routes of QIprojects PR 294 recorded in the SPIN-Z row). Reasoner is now on Mathlib v4.36.0 (`fc4f59e`); check which of these landed before that tag, the rest wait for the next bump.

**Design rule for headline 3:** state FIVE-0, FIVE-L and FIVE-U over `FixedWeightProblem` from the start, so FIVE-W is an instance (5-8k) rather than a second copy (15-25k).

## 3. Tier 2: off every headline path, and not planned

After the dependency check against the TeX (2026-11-25), every remaining package is on a headline path: `int:obstr` (INT-4) is cited by `int:cont-spin` and `pmix:main`, and `se:cdual` (DU-F) by `int:hb-reserve`, so both are tier 1. Tier 2 is therefore empty; section 3.1 lists what is not planned.

### 3.1 Not planned, with the reason

| item | labels | reason |
|---|---|---|
| **INT-L**, lattice integrality | `int:lat-reserve`, `int:poinc`, `int:amgm-floor`, `int:lat-repair`, `int:int-spin` | conditional on (CLM) (Chang-Liu-Ma, external) and on the SPIN-Z enclosures |
| N = 1 reduction | `n1:P1` | physics bookkeeping (characters, `eta^3/theta_3`); Lean takes the reduced problem as the definition |
| numerical decimals | `0.4837...`, `0.2070524`, `1.2180230048`, `21.0680128515`, `c_0^* = -0.0713301`, `d_2^* = -0.3462493`, tables of `ctu:table` | numerical evidence; the closed forms are in the planned packages |
| explicit Bessel constants | `vlo:BesselConst` (`kappa_0 = 1/4`, `kappa_1 = 1`) | not needed: Lean's constants are existential |
| vacuum-slack Theorem J | `int:Jslack` (alias of `vlo:J`) | used only by INT-L |
| unflavoured `N = (2,2)`, real weights outside `(H_w)` | main-text remark; `wone:ftlfw` for real `w` | `V = f_a * f_a` is not of Cardy type; the proof is a note neither Paper II document cites. Real `w` can be revisited after PM-0 |
| FT-3..6 beyond FT-CC | chart-form Lemmas 1-2 instances, C5d `m >= 2`, Lemma FT-R log rate | useful only for Paper I instances; the base `ChartCompactness` is tier 1 (FT-CC) because Paper I's `thm:intro-hb` (M8) needs it. Paper I's plan delegates `ft:L1`, `ft:L2`, `ft:riesz` (FT-3..6) and `fto1:mellin` (as `FT-7`, a package this plan does not have) to this lane, so neither plan owns them: unowned, pending an owner decision |
| five-term `c_0^*` clauses at weights not of the form `(H_w)` | `ctu:scope` remark | out of the paper's scope |

## 4. What is on master (compact record)

Unconditional, pinned axioms. "Scope" is the scope of the Lean statement, which is sometimes smaller than the paper's.

| result | TeX | Lean headline | scope |
|---|---|---|---|
| Lower bound `T_V >= T_* - C` | `wone:genlower`(1), `vlo:J` | `FixedWeightBand.fixedWeightLowerBoundInput_of_problem` | every `(w,Q)` in `(H_w)`; zero vacuum slack |
| Two-term law with `o(c^{1/3})` | `ds:E1` | `Upper.Assembly.virasoro_corollary_E1_littleO_unconditional` | Virasoro (also every weight-one `Q`: `thresholdUpperLittleO_prob`) |
| `O(1)` two-sided law, extremal crossing measure | `ds:E1`, first inequality of `ctu:O1` | `Upper.Ramped.theoremC15UpperInput_virasoro`, `virasoro_corollary_E1_unconditional`, `theoremC15UpperInput_prob`, `Upper.Assembly.n1_corollary_E1_unconditional` | every weight-one problem; for `w > 1` it is the hypothesis `TheoremC15UpperInput` |
| Property (P), `Sigma_0`, `Sigma` | `sr:P`, `sr:Sigma0`, `sr:Sigma` | `designPropertyP_virasoro`, `virasoro_sigmaZero_unconditional`, `virasoro_sigma_unconditional`, `sigma_unconditional_prob` | extremal measures of every weight-one problem; `f = 1` designs (far-first-site family replaces the paper's `f >= 2` Step 6) |
| Tip blow-up, Theorems C, R1-R3 | `bl:T`, `rig:R` | `proposition_T_of_problem`, `concrete_blowup_theorem_R3_general` | every `(w,Q)` (`Att` a hypothesis, as in the paper) |
| Crossing sum rule, strong duality, exact-gap measure | `fw:*`, `ds:D1`, `ds:M`, `ds:E` | `theorem_fwC_unconditional`, `FixedWeight.theorem_E`, `corollary_E1_exact_gap` | every `(w,Q)`; `ds:E` only for `F = empty`, `F = {t_1}`, and `X` containing a ray |
| Clark two-level curve, lower bound, `se:3.2` | `gt:2.1`, `wone:genlower`(2), `se:3.2` | `concrete_two_level_theorem`, `theorem_W1prime_two`, `A2star_lipschitzOn` | every `(w,Q)` |
| Two-level exclusion and Clark rigidity | `gt:2.4`-`gt:2.6` | `corollary_two_four`, `theorem_two_five_w1`, `theorem_two_six_w1_unconditional` | weight one; `theorem_two_five_of_T2`, `theorem_two_six_of_T2` for all `w` modulo `TwoSimpleZeroTransfer prob` |
| Theorem T2 | `ut:T2` | `twoSimpleZeroTransfer_of_w1` | weight one, `f = 2` |
| Fold-tip instances (Paper I's FT) | Paper I `ft:FT` | `FoldTip.ft_fixedWeight_general`, `ft_fixedWeight`, `ft_virasoro`, `ft_n1`, `fw_foldTip_hypotheses_w1`, `ft_twoEdge_lower_hb`, `ft_sub` | C1, C2, C3 (`O(1)`), C5a, C5b at every `(w,Q)`; C2 full, C4, C5c at `w = 1` |
| Bump at `w > 1`, packages P1-P4 | `ut:III`, K7 | `proposition_III`, `phase_packageP`, `bumped_phaseHyp`, `bump_floor` | every weight, `f = 1` designs; Proposition V and the `O(1)` upper bound remain (W-P5, W-P6) |

Done-package record (what each did and the lesson worth keeping; details are in the code and `THEOREM_MAP.md`):

- **A, O(1) upper bound at `w = 1`** (`Upper/Ramped/`, route U*). State the general lemma in our own file and re-derive the old
  declaration under its old name; a finite rational hole product, no Euler products; statements uniform in `d` and `C_I, C_mid`.
- **B, `Sigma_0`, `Sigma`** (`Upper/Rigidity`, `Upper/Assembly`): Property (P) for any bounded offsets; the omitted family is the
  `f = 1` far-first-site family (`farFamily`), the TeX keeps its `f >= 2` Step 6 with an internal note (owner decision).
- **C, N = 1** (`FixedWeightBand/N1Lower`, `Upper/Assembly/N1`).
- **TL1-TL6**, the two-level lane (`TwoLevel/`): `A2star` and `gt:2.1` (TL1); `windowOptimum` qualitative (TL2; its paper
  statement, the former Proposition 2.3, no longer exists, and `pmix:rigidity`(c) is the current statement); constrained
  duality and Corollary 2.4 (TL3); T2 in seven work packages WP1-WP7 and Theorems 2.5, 2.6 (TL4, TL5); W1'(2) with the Clark TE.0',
  Clark arc, node bounds and instance (TL6). Open follow-ups: `integrable` field of `TwoZeroTransferData`; a shared core builder
  for `bootstrapHB_of_YVForWThr`/`_Clark` (about 200 duplicated lines).
- **FT-0, FT-1, FT-2** (`FoldTip/`): concordance bundles, hypothesis structures H1-H4b with instances, FT-2E and FT-Sub over
  the two-edge bootstrap. The Lean `FTH4b` is the Airy-only form and does not match the paper's H4b: see FT-H4b below.
- **D, bump at `w > 1`**, P1-P4: weight-`w` bookkeeping (`qProb`, `CardyFarBoundP`), order-`p` comb transform and K7
  (`CombTransformP`, `PhaseComb`, `phase_packageP`), macroscopic bump (`Upper/Bump`), `R_p` calculus and Proposition III.

## 5. Scope caveats and inputs still carried as hypotheses

Statements that Lean proves only for a special case, so that nobody cites them as the paper's statement:

- `FixedWeightProblem` is integer `w` with a product `Q`. Everything labelled "every `(w,Q)`" above means that class; real `w`,
  mixtures and unflavoured `N = (2,2)` are outside it.
- `ds:E`: Lean has `X` containing a ray (`constrained_strong_duality`), `T_V = max` for `F = empty` (`theorem_E`) and the two-level
  `F = {t_1}`. `corollary_E1` and `ds:E1` give a crossing measure with gap exactly `T_V` and the `O(1)` law at weight one; atomicity
  is not stated.
- `TheoremC15UpperInput prob` is `T_V <= T_* + D_+` (the `O(1)` upper half). Its name and docstring in `FixedWeight/OptimalMeasure.lean`
  cite Theorem C15 / `thm:fixed-weight-expansion`, which are the five-term statements; no Lean statement of the five-term expansion exists.
  It is a theorem for `prob.w = 1` and the hypothesis of `corollary_E1`, `corollary_two_four_of_upper`, `ft_fixedWeight_H3` for `w > 1`.
- `TwoSimpleZeroTransfer prob` (T2) is a theorem for `prob.w = 1` and the hypothesis of `theorem_two_five_of_T2`,
  `theorem_two_six_of_T2` for `w > 1`.
- `designPropertyP_*` and `Sigma` are for the extremal measures of weight-one problems, with the far-first-site omitted family.
- `gt:2.1` is for weakly feasible tests (`g_vac >= 0`), not for measures with vacuum slack (`bl:norm`, SLK).
- `windowOptimum*` (`TwoLevel/WindowOptimum*`, 1.7k lines) proves a qualitative window optimum with decay `K^{-1/15}`; the paper no longer
  states it (the former Proposition 2.3).
- Planned named hypothesis (owner decision): `SpinZEnclosures`, the Arb interval enclosures of the integer-spin proof (SPIN-Z); headline 1's integer-spin half is proved modulo it until the certificates are done.
- Named input structures that are still hypotheses somewhere: `TheoremC15UpperInput` (`w > 1`), `TwoSimpleZeroTransfer` (`w > 1`),
  `FTH3`, `FTH4b` (`w > 1`; `FTH4b` is also the wrong form, see FT-H4b), `DesignPropertyP` for non-design families.
  Inputs that earlier plans listed and that are now proved: `MehlerOddMomentInput`, `BesselI0Asymptotic`, `BesselComplexExpansion`,
  `SDVAmplitudeInput` (for design combs), `ShiftSumEstimate`, `TwoZeroIdealApprox`, `DesignTailBounds`.

## 6. Boundary with the Paper I session, and the fold-tip interface

- Paper I owns `SignUncertainty/`, `CohnElkies/`, `TwoEdgeBootstrap/`, `Special/Airy*`, `Complex/`, `Analysis*`, `Asymptotics/`
  (plan: `FormalResearch/SignUncertainty/PLAN.md`). Paper II imports `TwoEdgeBootstrap` (`teb_bootstrap_part1`) and `Special` and does
  not edit them; the recalled results of 3.10 map to Paper I's Lean as listed there.
- Their M5 plans to refactor the Virasoro `ArcBounds`/`QuadratureBounds` for the Hankel TE.3 instance. `FixedWeightBand/BootstrapW*`
  already generalises those instances to every weight `w`; the Hankel instance should start from that pattern. Paper II does not
  refactor `ConcreteBootstrap/` or `TwoEdgeBootstrap/`.
- Langer charts are separate objects (Paper I: Hankel/Bessel density, `gt:7.7b/c/p`; Paper II: the Virasoro comb density,
  `Ramped/LangerTau*`). Mellin strips likewise (`SignUncertainty/MellinStrip*` for the Hankel kernel, `FixedWeightBand/Mellin*W` for the
  weight-`w` Bessel weight). No duplication.
- **Fold-tip (FoldTip interface).** Theorem FT is a theorem of Paper I (Section 4, `fold_tip_universality.tex`, `fold_tip_two_edge.tex`,
  `fold_tip_instances.tex`), not of Paper II; its Lean code is `ModularBootstrap/FoldTip/` because Paper II's instances use it. FT-0, FT-1,
  FT-2 are done (imports `TwoEdgeBootstrap`, edits nothing there); `TwoEdgeBootstrap/FoldTipSeed.lean` serves only Lemma L (H3 from a
  lift) and is not used. For Paper II's own instances (Virasoro, `N = 1`, fixed `(w,Q)`) the conclusions C1, C2, C3 (`O(1)` form), C5a, C5b
  and C5c at `w = 1` are proved by other routes; FT reuses those proofs (no refactor of Prop T, Theorem R or `Sigma` through FT: about
  8k lines at stake for little gain).
- **Agreed interface** with Paper I (`SignUncertainty/PLAN.md`, section 5): `HermiteBiehlerData` lives in
  `SignUncertainty/HermiteBiehlerData.lean`; the base structure `ChartCompactness` (`compactness_subseq` plus site and tail positivity, for an
  abstract setting, importing nothing Hankel- or Virasoro-specific) is owned by this lane; Paper I adds, without editing `RadialRigidity.lean`,
  a converter `RadialRigidityPackage -> ChartCompactness`; Paper I's M8 TE.0' is a converter into `ChartCompactness` plus the shared rigidity
  theorem. Steps 3 and 4 start when `ChartCompactness` is on `master`; it is not there yet (no declaration of that name). Paper I's
  `lem:qual-compact` (qualitative mass transfer, new in `airy_extremal.tex`) is not in Lean; check `SignUncertainty/` before adding it for
  FT-3..6 or `bl:norm`.
- Paper I does not plan Lemma WP, Lemma WR or `teb:quant_c1_near`; here they are FT-H4b and FIVE-L.
- TE.0' beyond `alpha = 0`: Paper I's M8 is the Hankel type-(I) instance for polynomial `(P,Q)`; Paper II does the Airy type-(II) constant-Clark-pair
  instance in `ConcreteBootstrap/QuantC1Clark.lean` (done) and does not edit `QuantC1Airy.lean`, which Paper I's `HankelQuantC1` imports.
- Shared files: the umbrella `FormalResearch/ModularBootstrap.lean` and `THEOREM_MAP.md` (targeted edits after merging `origin/master`;
  never apply an agent's stale umbrella as a diff).

## 7. Reference: coverage table, every stated result

One row per coherent set of results with one proof route. Labels are the first `\label` of each result (aliases in
Appendix A); the file is in `CFT/modular_bootstrap/paper/`. Columns: **Lean today** names declarations (each was grepped in
`FormalResearch/`; no file contains a proof placeholder or a non-pinned axiom); **scope / still a hypothesis** is what the Lean statement
does and does not cover; **remaining** names the work packages of sections 2 and 3. Per-label states are in Appendix A; where a row mixes
states they are listed in the row.

### 7.1 Crossing and the lower side

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **CR** Crossing sum rule | `fw:abel`, `fw:crossing`, `fw:FWC` (crossing_sum_rule) | `Crossing/`: `lemma_fwA_part1_unconditional`, `_part2_`, `_part3_unconditional` (FW-A), `lemma_fwX_one_sided_unconditional`, `lemma_fwX_equality_unconditional`, `crossing_counting_bound` (`fw:counting`), `theorem_fwC_unconditional`, `theorem_fwC_le_T_V_unconditional`; the setting `FixedWeightProblem`, `TestClass`, `T_V`, `Delta_best` | every integer `w >= 1`, product `Q` (`(H_w)`); no mixtures, no real `w`. The originals in `SumRule.lean` still take `MehlerOddMomentInput` as an argument; it is proved (`mehlerOddMomentInput`), so cite the `_unconditional` forms | mixtures: PM-0 | L, 7.5k | 3 done |
| **LB1** Virasoro slit-strip and Bessel lemmas | `vlo:Bessel`, `vlo:BesselConst`, `vlo:Gap`, `vlo:PJ` (lower_o1_two_edge) | `Bessel/*` (`besselV_asymptotic`, `besselK_le_mul_besselV`), `ComplexBessel/*` (`besselI0C_sector_asymptotic`), `WeightAxioms/*` (`besselIC_sector_asymptotic`, `fixedWeightAxioms_of_problem`), `PoissonJensen/*` and `SlitStrip/*` (`stripPoissonJensen`, `harmonicMajorantIdentification`), `TipFront/*` (`stripPoissonJensen_complex`), `FixedWeightTip/PoissonJensenGeneral` (`stripPoissonJensen_general`, `lemmaG_of_problem`), `Integration/*` (`theoremA_Delta_best`) | Lemma G and PJ at every integer `(w,Q)`; Lemma B(c) at real `x` and complex sectors. Lemma B': constants are existential (`C` in `besselI0C_sector_asymptotic`). Per label: `vlo:BesselConst`: existential constants only; the explicit `kappa_0 = 1/4`, `kappa_1 = 1` are not needed downstream (not planned) |  | L, 25k | 3 done, 1 partial |
| **LB2** Mellin chart, strip band bound, truncation, scale choice | `vlo:S1`, `vlo:S2`, `vlo:S3`, `vlo:S4`, `vlo:S5`, `vlo:S6`, `vlo:J40`, `vlo:J41`, `vlo:J42`, `vlo:YV`, `vlo:XV`, `vlo:E2`, `vlo:F`, `vlo:Zp`, `vlo:J7Q`, `vlo:Dp`, `vlo:Z`, `vlo:L`, `vlo:J10escape` (lower_o1_two_edge) | Virasoro: `Mellin/*` (`lemma_S1`), `ComplexBessel/LemmaS2` (`lemma_S2`), `Chart/*` (`lemma_S3_positivity`, `lemma_J4_0`, `lemma_S5_deriv`, `lemma_S6`, `lemma_E2_E3`, `lemma_F`), `ChartGeometry/*` (`lemma_J7Q`, `lemma_J10_compact_escape`), `StripMultiplier/*` (`lemma_S4`, `lemma_J4_1`, `lemma_J4_2`, `proposition_YV`, `proposition_XV_of_bootstrap`), `Contour/*` (`lemma_Zp`, `lemma_Dp`, `lemma_Z`); every `(w,Q)`: `FixedWeightBand/` (`lemma_S1_W`, `lemma_S2_W`, `lemma_S4_W`, `lemma_J4_1_W`, `lemma_J4_2_W`, `proposition_YV_W`, `proposition_XV_W`, `lemma_Dp_W`, `lemma_Z_W`, `stirlingFW`) | every integer `(w,Q)`, `A_thr` uniform on compacts. Proposition L (`vlo:L`) has no standalone statement: it is absorbed in the scale choice (`LemmaQData.bvChoice`, `Contour/VirasoroScaleChoice`) |  | L, 40k | 19 done |
| **LB3** Fold-tip lower bound at every fixed weight | `ft:PP`, `vlo:J`, `wone:ftlfw`, `wone:genlower` (lower_o1_two_edge) | `FixedWeightTip/PropositionP` (`proposition_P_of_problem`, Lemma Q), `FixedWeightBand/` (`LemmaQData`, `theoremFTLFW_W_of_YVFor`, `fixedWeightLowerBoundInput_of_problem`: Theorem J / W1'(1) for every `(w,Q)`), `ConcreteBootstrap/*` (Virasoro chain, `theoremJ_Delta_best`), Clark pair (`BootstrapClark*`, `teb_quant_c1_clark_typeII`, `bootstrapHB_of_YVForClark`, `twoEdgeInstance_of_YVForClark`, `theorem_W1prime_two`), `FoldTip/TwoEdge*` (`ft_twoEdge_lower_hb`, `ft_fixedWeight_twoEdge`) | integer `w`; `FixedWeightLowerBoundInput prob` is the exact shape of W1'(1). The paper states FT-L.FW for real `w >= 1` under (W1)-(W4); Lean's chain takes `prob : FixedWeightProblem`. Per label: `vlo:J`: zero vacuum slack only; the slack clause (alias `int:Jslack`) is used by INT-L only (not planned); `wone:ftlfw`: Lean has the Airy level `m_0 = 1` and the Clark pair `m_0 = 2`; general Hermite-Biehler `(P,Q)` and real `w`: HB1 / WA; `wone:genlower`: Lean has parts (1) and (2) (`m_0 = 1, 2`); general `m_0`: HB1 | HB1; real `w` / mixtures: PM-0 | L, 25k | 2 done, 2 partial |

### 7.2 Blow-up, rigidity, weight axioms

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **BL** Tip blow-up of weakly feasible tests | `bl:T`, `bl:T1`, `bl:T2`, `bl:T4`, `bl:T5`, `bl:norm` (blowup_limit) | `Blowup/*` (`lemma_T1`, `lemma_T2`, `lemma_T4`, `lemma_T5`, `proposition_T`); every `(w,Q)`: `FixedWeightTip/BlowupAndRigidity` (`lemma_T5_general`, `proposition_T_general`, `proposition_T_of_problem`); `TipFront/*` (concrete `BlowupTest`s). Lemma T3 (Stirling) is `lemma_T3_unconditional` | tests with `g_vac >= 0`; Proposition T(v) has the lower cutoff `s > -xi_*/eps` that the paper omits | `bl:norm` (HB level, `m_0 >= 1`, with vacuum slack, `L^1` convergence): SLK | L, 8k | 5 done, 1 planned |
| **RG** Airy-level rigidity at fixed weight | `rig:R` (rigidity) | `Rigidity/AiryRigidity` (`local_sign_uncertainty`, `theorem_C`, `theorem_C_real`, `theorem_R1`, `theorem_R2`, `theorem_R3`), every `(w,Q)`: `concrete_blowup_theorem_C_general`, `concrete_blowup_theorem_R1_general`, `_R2_general`, `_R3_general`, `att_of_upper_threshold_general` | every integer `(w,Q)`; `Att` is a hypothesis of Theorem R as in the paper |  | M, 1.4k + 2k | 1 done |
| **W** Weight axioms, N = 1 NS super-Virasoro | `n1:L4`, `n1:L2`, `n1:P1`, `n1:T3`, `n1:T5` (n1_super_virasoro) | `WeightAxioms/*` (`fixedWeightAxioms_of_problem`, `lemma4_summary`, `n1SuperVirasoro_fixedWeightAxioms`), `FixedWeightBand/N1Lower`, `Upper/Assembly/N1` (`n1_designPropertyP`, `n1_theoremC15UpperInput`, `n1_corollary_E1_unconditional`, `n1_sigmaZero_unconditional`, `n1_sigma_unconditional`), `FoldTip/Concordance` (`ft_n1`) | `n1SuperVirasoroProblem` only (weight one); unflavoured `N = (2,2)` and real weights are outside `FixedWeightProblem`. Per label: `n1:L2`: instance of L4; the explicit `v_2 = 2 pi^4` comparison is not stated; `n1:T3`: lower half (`n1_lowerBoundInput`, `n1_T_V_lower`), `O(1)` law (`n1_corollary_E1_unconditional`), `Sigma_0`, `Sigma`; five-term and the rest of T5: FIVE-W, DU-G, PA1, LP1, HB1, INT-3; `n1:T5`: umbrella: items proved in Lean are the lower bound at every `(w,Q)`, duality for `F = empty`, the Clark boundary at `w = 1`, `se:3.2` | see rows | L, 5.4k + 1k | 2 done, 2 partial, 1 not planned |

### 7.3 Upper side: estimates, designs, rigidity

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **ESD** Edge transform and two-saddle descent | `esd:asym`, `esd:hankel`, `esd:global`, `esd:phase`, `esd:lemmap`, `esd:lemma` (edge_transform_sd) | `Upper/Hankel/*` (`hankel0_expansion`, `norm_hankel0_le`, `edge_hankel_representation`, `edge_global_bound`; order `p`: `hankelOrd_expansion`, `hankelTransformOrd_eq_iterate`, `edge_hankel_representation_P`, `edge_global_bound_P`), `Upper/Saddle/*` (`lemma_SD_V_prime`, `lemma_SD_V`, `lemma_FW_SD_part2`, `edgePhaseData_blaschke`) | abstract hypotheses structures (`EdgePhaseData`, `SDVHypotheses`, `FWSDHypotheses`) are instantiated for the Blaschke combs and design profiles (`design_sdvAmplitudeInput`) |  | L, 13k | 6 done |
| **CMB** Reference comb, holes, Langer coordinate, Cardy weight | `cmb:K0`, `cmb:K1`, `cmb:K2`, `cmb:K3`, `cmb:K4`, `cmb:K5`, `cmb:K6`, `cmb:K7`, `cmb:K8`, `rem:analytictip`, `rem:analyticII`, `rem:cardy`, `rem:P1.1`, `rem:P1.2` (comb_estimates, remainder) | `Upper/Comb/*` (`riesz_representation`, `refComb_K1a`, `edgePhase_bounds`), `Upper/Holes/*` (`hAII_min_at_half`, `regionII_margin_gt`, `hole_lower_K4`, `hole_upper_K4`, `hole_limit_K5`, `band_upper_K6a`, `lobe_upper_K6b`), K7: `k7_membership_vacuum`, `design_k7_membership_vacuum`; `Upper/Window/CardyWindow` (`besselV_window_bound`, `besselV_far_bound`, `cardyWindowBound_prob`), `Upper/Ramped/Langer*` (`langerTau_spec`, `langerChart_F1`, `langerChart_F2`), `Upper/Ramped/CombToAiry*` (`combToAiry_mult`, `combToAiry_log_rate`) | K7 at weight one for the reference comb and for design combs; `rem:cardy` at every weight (`cardyWindowBound_prob`). Per label: `rem:cardy`: stated as a `remarkx` named Lemma A_V; `rem:P1.1`: closed form `C_* = 4 pi sqrt kappa`; the decimal 21.068... is numerical only |  | L, 30k | 14 done |
| **UTW** Design lemmas (weight-free) and fixed-order membership | `ut:Z`, `ut:P`, `ut:Phi`, `ut:W`, `ut:ID`, `ut:G`, `ut:V`, `ut:E`, `fw:FWM`, `fw:SDp` (upper_transfer) | `Upper/Window/Product` (`deltaWKB_le_exists` = Lemma Z; `lemma_G_bound`, `lemma_V_identity`, `lemma_E`), `Upper/Design/*` (`lemma_P_b`, `lemma_Phi_b`, `lemma_Phi_transform`, `lemma_Phi_transform_of_phase`), `Upper/Window/{WindowLimit,Identification}` (`lemma_W_comb`, `lemma_W_measure`, `lemma_ID`, `lemma_ID_design`), `Upper/Ramped/*` (`lemma_P_unif`, `lemma_G_bound_unif`), `Upper/Membership/*` (`fwM_membership_vacuum`, `design_k7_membership_vacuum`, `K7ConclusionW`), order `p`: `phase_packageP` | Lemma P(a) for fixed `N` and in the profile-uniform form `lemma_P_unif`; FW-M at every weight by radial Fourier inversion on `R^{2w}` |  | L, 20k | 10 done |
| **UTP** Positivity and vacuum of the designs | `ut:II`, `ut:R`, `ut:I`, `ut:IIF`, `ut:III`, `ut:T`, `ut:Vac` (upper_transfer) | `Upper/Positivity/*` (`proposition_II`, `proposition_II_design`, `proposition_I_design_t`, `proposition_I_sigW`, `proposition_III`, `proposition_III_regionII`, `bumped_regionII`, `vacuum_core`, `proposition_V_i`), `Upper/Window/{LemmaR,Tail}` (`lemma_R`, `lemma_R_lower`, `lemma_T`, `lemma_T_prob`, `lemma_T_design1`), `Upper/Bump/*` (`bumpFactor`, `bumped_phaseHyp`, `bump_floor`), `Upper/Positivity/RpAmplitude*` | `Upper/Ramped` (the route to the `O(1)` bound) is not a paper result; see UP. Per label: `ut:I`: `f = 1` designs; `proposition_I_sigW` at every weight; real factors `f >= 2`: W-T2w / W-P5; `ut:IIF`: `f = 2, r = 1` only (`proposition_II_floor`, `twoZero_regionII`); `bumped_regionII_pos` any `f` at every weight; `ut:III`: `f = 1` designs with the bump at every weight (`proposition_III`); finite real factors: W-T2w; `ut:T`: Virasoro and `w = 1` (`lemma_T`, `lemma_T_prob`); any weight only through the interface `lemma_T_of_cardy`: W-P5; `ut:Vac`: `w = 1`, `f = 1` designs (`proposition_V_i`, `proposition_V_ii`); every weight: W-P5 | W-P5 (Prop V, Lemma T at weight `w`), W-T2w | L, 11k | 2 done, 5 partial |
| **T2** Two-simple-zero transfer, ideal windows, Prop W1.5 | `ut:T2`, `ut:ideal`, `wone:clark` (upper_transfer) | `TwoLevel/TwoZero*` (5.6k: WP1 `TwoZeroDict`, WP2 `TwoZeroComb{K7,Phase,T}`, WP3 `TwoZeroRegionTwo`, WP4 `TwoZeroRegionOne`, WP5 `TwoZeroWindow`, WP6 `TwoZeroVacuum`, WP7 `TwoZeroTransferProof`: `twoSimpleZeroTransfer_of_w1`, `twoZero_limsup_field`, `twoZero_pos_t`), `TwoLevel/IdealApprox*` (`twoZeroIdealApprox`) | `prob.w = 1`; the named `Prop TwoSimpleZeroTransfer prob` is the hypothesis for `w > 1`. Follow-up: add an `integrable` field to `TwoZeroTransferData`. Per label: `ut:T2`: weight one (`twoSimpleZeroTransfer_of_w1`); weight `w > 1` and Remark T2.1 (more real zeros): W-T2w; `ut:ideal`: `m = 2` (`twoZeroIdealApprox`); general `m`: W-T2w; `wone:clark`: (c) at `w = 1` (`wone_clark_two_level_boundary`); (a) at `w = 1`; (b) and all weights: W-P5, W-T2w | W-T2w | L, 7.4k | 3 partial |
| **SR** Property (P) and spectral rigidity of the near-extremal measures | `sr:P`, `sr:Sigma0`, `sr:Sigma`, `sr:cor`, `sr:single-level` (spectral_rigidity) | `Upper/Rigidity/*` (`theorem_Sigma`, `theorem_sigma_zero_a`, `theorem_sigma_zero_b`, `spectral_poisson_summation`, `spectral_complementary_slackness`, `gapCondition_of_lowerBound`, `exists_optimalCrossingSequence`, `theorem_sigma_crossing`), `Upper/Assembly/*` (`designPropertyP_virasoro`, `displacedPropertyP_virasoro`, `farFamily`, `virasoro_sigmaZero_unconditional`, `virasoro_sigma_unconditional`, `designPropertyP_prob`, `sigmaZero_unconditional_prob`, `sigma_unconditional_prob`) | unconditional for the extremal measures of every weight-one problem (hypothesis `Gap` discharged by the lower bound); `Sigma` states the vague limit of `mu_S`; the t-space corollary is not stated. Per label: `sr:P`: `f = 1` designs, displaced sites, far-first-site omitted family (`farFamily`), every `w = 1` problem; the TeX keeps its `f >= 2` Step 6 with an internal note (owner decision). Every weight: W-P5; `sr:Sigma0`: every `w = 1` problem for the extremal measures; every weight: W-P5; `sr:Sigma`: same; every weight: W-P5 | W-P5, SR-COR, PA2 | L, 8k | 3 partial, 2 planned |
| **UP** O(1) upper bound at weight one (route Lemma U*, no paper label) | (no paper label) (n2_ramped_comb (note), dual_spectrum) | `Upper/Ramped/*` (19k, R1-R8): `theoremC15UpperInput_virasoro`, `theoremC15UpperInput_prob` (`w = 1`, every `Q`), `rampedG_isFeasible`, `rampedVacuum_prob`; `Upper/Assembly/Feasible` (`virasoro_thresholdUpperLittleO`, `thresholdUpperLittleO_prob`, `virasoro_corollary_E1_littleO_unconditional`) | `TheoremC15UpperInput prob` means `T_V <= T_* + D_+` (the `O(1)` upper half). Its name and docstring (`FixedWeight/OptimalMeasure`) cite Theorem C15 / `thm:fixed-weight-expansion`, which is the five-term statement. Proved for `prob.w = 1`; hypothesis for `w > 1` | W-P6 | L, 19k | done at `w = 1` |

### 7.4 Two-level curve and soft-edge stability

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **TL** Clark two-level curve and soft-edge two-level bounds | `gt:2.1`, `gt:2.4`, `gt:hb`, `se:3.2`, `se:3.3`, `se:cdual`, `se:terminal-stability`, `se:3.1` (virasoro_two_level, soft_edge_two_level_stability) | `TwoLevel/` (15k): TL1 `A2star`, `A2star_mem_Ioo`, `A2star_strictMonoOn`, `A2star_lipschitzOn`, `concrete_two_level_theorem`, `concrete_two_level_equality`; TL3 `constrained_strong_duality`, `constrained_strong_duality_two_level`, `corollary_two_four`; TL4 `theorem_two_five_w1`, `theorem_two_five_of_T2`, `theorem_two_six_w1_unconditional`, `theorem_two_six_of_T2`, `tendsto_atom_weight_of_T2`; TL6 `theorem_W1prime_two`, `concrete_two_level_theorem_O1`, `n1_two_level_lower`, `theorem_SE7_uniform`, `wone_clark_two_level_boundary`; `windowOptimum_lt`, `tendsto_windowOptimum`, `isGLB_window_amplitude` (qualitative; the former Proposition 2.3 is no longer in the paper) | `corollary_two_four_of_upper` needs `TheoremC15UpperInput` for the positive mass at `t_1`. Per label: `gt:2.1`: tests at every `(w,Q)`; mixtures: PM-3; `gt:2.4`: the one result Corollary 2.2 with aliases `gt:2.4`, `gt:2.5`, `gt:2.6`: unconditional at every `w = 1` problem; every `w` under `TheoremC15UpperInput` (2.4) and `TwoSimpleZeroTransfer` (2.5, 2.6): W-P6, W-T2w; mixtures: PM-3; `gt:hb`: Airy `m_0 = 1` (`rig:R`) and Clark `m_0 = 2` only; general `(P,Q)`: HB1; `se:3.2`: `theorem_W1prime_two` (every `(w,Q)`, `A_1` in compacts of `(-inf, A_opt)`); `theorem_SE7`, `theorem_SE7_uniform` are the Virasoro `O(log c')` forms; `se:cdual`: `F = {t_1}` duality only (`constrained_strong_duality_two_level`): DU-F | W-P6, W-T2w, HB1, STAB, SE3, DU-F, PM-3 | L, 15k | 2 done, 3 partial, 3 planned |
| **STAB** Stability of the equality cases and size of the violation | `rem:thmBstab`, `rem:thmL`, `rem:corL`, `rem:thmOloc` (remainder, soft_edge_two_level_stability) | `LStar_eq_half_norm_integral`, `localExtremalC`, `theorem_C` (local model, `Constants.lean`, `Rigidity/AiryRigidity`) give `L_*`; no infimum-slope statement `I(delta)/delta` | Per label: `rem:thmL`: recalled from Proposition P Step 2 at `w = 1`: `lemmaQ_part1At_of_general`, `proposition_P_of_problem`; `rem:corL`: Airy and Clark `C^1` stability and the envelope exist (`teb_quant_c1_typeII`, `teb_quant_c1_clark_typeII`); the packaged corollary (a)-(c) is not stated: FIVE-L | STAB, FIVE-L | M | 1 done, 1 partial, 2 planned |

### 7.5 Duality, attainment, infinite-order limit

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **DU** Duality, crossing measures, Corollary E1 | `ds:D1`, `ds:M`, `ds:farkas`, `ds:E`, `ds:E1` (dual_spectrum) | `Duality/*` (2.4k; Virasoro): `proposition_D1`, `lemma_M`, `theorem_E`, `theorem_E_b`, `theorem_E_c`, `corollary_E1_exact_gap`, `corollary_E1_lower_bound`; `FixedWeight/*` (2.9k; every `(w,Q)`): `proposition_D1`, `lemma_M`, `theorem_E`, `corollary_E1`, `corollary_E1_exact_gap`, `virasoro_corollary_E1_exact_gap`; `Upper.Ramped.virasoro_corollary_E1_unconditional`, `Upper.Assembly.n1_corollary_E1_unconditional` | `corollary_E1` takes `FixedWeightLowerBoundInput` (proved) and `TheoremC15UpperInput` (proved at `w = 1`) as hypotheses. Lean statements are for integer `w` and product `Q` and do not state atomicity. Per label: `ds:farkas`: finite-family Farkas with weak compactness (`farkas_approx`, `exists_atomic_approx`, `exists_measure_exact`); the positive-extension-with-moment-bound statement is not stated: DU-G; `ds:E`: (a) for closed `X` containing a ray (`constrained_strong_duality`), (b) `T_V = max` for `F = empty` and `F = {t_1}`, no (c) reserve separation: DU-G; `ds:E1`: crossing measure with gap exactly `T_V` and the `O(1)` law at `w = 1`; atomicity and `w > 1`: PA1, W-P6 | DU-G, PA1, W-P6, PM-4 | L, 5.3k | 2 done, 3 partial |
| **PA** Primal attainment, atomicity, one-level clusters | `dsl:strip-fixed`, `ds:primal`, `dsl:one-level-clusters`, `dsl:near-opt-mass` (dual_spectrum, dual_spectrum_limit) | none (`grep primal` finds only Farkas/compactness helpers). Rigidity ingredients exist (`Upper/Rigidity/{Atoms,Concentration,Weights,Nodes}`) | `sr:Sigma`-type results in Lean are for the designs and extremal measures `nu_*` of the O(1) law, not for every attaining measure | PA1, PA2 | L | 4 planned |
| **LP** Infinite-order derivative limit | `ds:LP`, `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact` (dual_spectrum, dual_spectrum_limit) | Farkas step and weak-`*` compactness only (`Duality/Farkas`, `Duality/MeasureCompactness`); no Laguerre moment bound, no `dsl:poly-compact` |  | LP1 | M-L | 5 planned |

### 7.6 Five-term expansion

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **FIVE0** Five-term constants: Langer chart, phase locking, outer function, exact minimum | `cts:langer`, `cts:phaselock`, `cts:involution`, `cts:main`, `ctu:piece4`, `ctu:jets`, `ctu:common-functional` (constant_term_slit_strip, constant_term_universality) | none (`Constants.lean` has `xiStar`, `lambdaV`, `Aopt_eq_closed`, `phiStar`; no `c_0^*`, `c_1^Langer`, `d_2^*`, no outer function on the half-disc) |  | FIVE-0 | L | 7 planned |
| **FIVEL** Five-term sharp lower bound | `cts:edge-hankel`, `cts:cauchy-dual`, `cts:rosc-uncond`, `cts:boas`, `cts:lower-main`, `ctl:dyadic`, `ctl:pass2`, `ctl:freeze` (constant_term_slit_strip, constant_term_lower_log) | none; the `O(1)` lower bound (`theoremJ_Delta_best`, `theorem_W1prime_two`) and the `C^1` stability (`teb_quant_c1_typeII`) are its inputs |  | FIVE-L | L | 8 planned |
| **FIVEU** Five-term sharp upper bound (exact comb with smoothing) | `cts:smooth-env`, `cts:tip-shared`, `cts:upper-design`, `cts:regionII-floor`, `cts:shifted-langer`, `pm:tip-match`, `cts:upper-vac`, `cts:transfer` (constant_term_slit_strip) | none; its inputs `esd:*`, `cmb:K1`, `K4`, `K7`, `ut:G` are in Lean (ESD, CMB, UTW) |  | FIVE-U | L | 8 planned |
| **FIVEW** Five-term expansion at fixed weight | `ctu:main`, `ctu:O1`, `ctu:table`, `ctu:weight`, `ctu:strip`, `thm:fixed-weight-expansion`, `thm:spinless-expansion` (constant_term_universality, modular_bootstrap_gap_proof) | none beyond the `O(1)` law above | Per label: `ctu:O1`: the first inequality (`O(1)` law) at `w = 1` is `virasoro_corollary_E1_unconditional`, `n1_corollary_E1_unconditional`; every weight: W-P6; the clauses with `c_0^*`, `c_0^*(w,Q)`: FIVE-W | FIVE-W | L | 1 partial, 6 planned |

### 7.7 Positive mixtures

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **PM** Positive finite mixtures | `pmix:rebase`, `pmix:weight`, `pmix:crossing`, `pmix:jets`, `pmix:punif`, `pmix:ramped`, `pmix:smooth`, `pmix:o1`, `pmix:vac`, `pmix:duality`, `pmix:hbphase`, `pmix:hbtap`, `pmix:rigidity`, `pmix:main` (positive_mixtures) | none; `WeightAxioms/` states (W1)-(W4) for one product vacuum. `pmix:punif` is the Airy-profile estimate that Lean has in the form `lemma_P_unif`/`pUnif_bound` (`Upper/Ramped`), weight-free |  | PM-0 ... PM-5 | L | 14 planned |

### 7.8 Integrality

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **INT** Integrality (thermal) | `int:int-closed`, `int:cheb`, `int:sonine`, `int:repair`, `int:shell-inv`, `int:atom`, `int:reserve`, `int:strict-weak`, `int:hb-reserve`, `int:main`, `int:obstr` (integrality) | none (`grep int:` finds only the `ft`/`sr` crossing-measure helpers) |  | INT-T, INT-1, INT-2, INT-2HB, INT-3, INT-4 | L | 11 planned |
| **INTL** Integrality on the full modular lattice | `int:lat-reserve`, `int:poinc`, `int:amgm-floor`, `int:lat-repair`, `int:int-spin` (integrality_lattice) | none |  | INT-L (not planned: (CLM)-conditional) | L | 5 not planned |
| **INTS** Integrality with continuous spin | `int:axis-trace`, `int:cheb2d`, `int:cos2d-repair`, `int:cont-spin` (integrality_spin) | none |  | INT-S | L | 4 planned |

### 7.9 Spin

| pkg | labels (file) | Lean today | scope / still a hypothesis | remaining | size | label states |
|---|---|---|---|---|---|---|
| **SPINF** Continuous spin: foundations and calibration | `spinnotes:S1`, `spinnotes:S21`, `spinnotes:S22`, `spinnotes:S22b`, `spinnotes:S23`, `spinnotes:S24`, `spinnotes:S3`, `scal:C1`, `scal:C3` (spinning_foundations, spinning_calibration) | none | analytic | SPIN-F | L | 9 planned |
| **SPIND** Continuous spin: duality and the Airy law | `sd:M`, `sd:T`, `sd:P`, `sd:SD`, `sd:W`, `sd:V`, `sd:A`, `sd:LP`, `sd:R` (spinning_dual) | none |  | SPIN-D | L | 9 planned |
| **SPIN4** Continuous spin: sharp Airy coefficient | `s4:S4`, `s4:2.1`, `s4:2.2`, `s4:2.3`, `s4:2.4`, `s4:3.3`, `s4:3.4`, `s4:4.1`, `s4:4.2`, `s4:4.3`, `s4:5.1`, `s4:5.2`, `s4:6.1`, `s4:4.4` (spinning_s4) | none |  | SPIN-S4 | L | 14 planned |
| **SPINZ** Integer spin (interval enclosures) | `spinnotes:K1`, `spinnotes:K2`, `spinnotes:K3`, `spinnotes:K4`, `spinnotes:K4a`, `spinnotes:L0a`, `spinnotes:L0b`, `spinnotes:L1`, `spinnotes:L2`, `spinnotes:L3`, `spinnotes:L4`, `spinnotes:L5`, `spinnotes:L6`, `spinnotes:L7`, `spinnotes:L8`, `spinnotes:L9`, `isl:main`, `isl:finite` (spinning_integer_*) | none | enclosures as `SpinZEnclosures` (owner decision) | SPIN-Z (tier 1, wave 5) | M | 18 planned |

### 7.10 Results recalled from Paper I (`recalled_paper1.tex`)

These are stated in Paper II without proof and belong to Paper I's plan (`FormalResearch/SignUncertainty/PLAN.md`) and Paper I's
Lean (`Special/`, `SignUncertainty/`, `TwoEdgeBootstrap/`); they are not Paper II packages. Two of them have their Lean in this
lane's directories because Paper II's instances needed them (`gt:1.0`, `teb:kernel`, `teb:mellin`, `teb:quant_c1`).

| label | result | Lean today | status |
|---|---|---|---|
| `ap:thmD` | Theorem D (Airy defect) | `airy_defect_ball`, `airy_defect_bound`, `airyNC_defect_bound` (`Special/AiryCft*`) | formalised |
| `ap:corD1` | Corollary D1 (`nu < -1`) | `airy_quadrature` (`Special/AiryCftQuadrature`) | formalised |
| `ap:lemH` | Lemma H (Hardy space) | none; route avoided (`airyQ_sampling` via Fejer-Riesz bounds, `Complex/Hardy*`) | not formalised, not used |
| `ap:lemFR` | Lemma FR (arc bound) | none as a statement; the arc bounds Paper II uses are `airy_defect_ball_split`, `clark_defect_ball_split_uniform`, `quad_arc_boundClark_uniform` | not formalised as stated |
| `ap:lemHp` | Lemma H' | none | not formalised, not used |
| `ap:thmQ` | Theorem Q | `airyQ_hasSum_unc`, `airyQ_sampling`, `airyQ_pointwise_sharp`, `airyNC_hasSum_unc` | formalised (parts (1)-(4)) |
| `lam:thmB` | Theorem B | `airy_sign_uncertainty`, `airy_sign_equality_iff` | formalised |
| `gt:1.0` | Lemma 1.0 (good circles, `psi_alpha`) | `clark_good_circle_at`, `clark_good_circle_uniform` (`ModularBootstrap/ConcreteBootstrap/ClarkDiscBoundsUniform`, Paper II lane) | formalised |
| `gt:1.0p` | Lemma 1.0' (HB good circles) | `airyPQ_good_circle` (`Special/AiryPolyCircle`) | formalised |
| `gt:1.0pp` | Lemma 1.0'' (finite-Blaschke Airy quadrature) | `airyPQ_hasSum_unc`, `airyPQ_lemma44_hasSum` (`Special/AiryPoly*`) | formalised for `Q != 0` |
| `gt:1.1` | Theorem 1.1 (Clark-Airy summation) | `airyClark_quadrature`, `airyClark_hasSum_unc` | formalised |
| `lem:hb-uniqueness` | Lemma H.2a | `hb_uniqueness` (`SignUncertainty/HermiteBiehlerUniq`) | formalised |
| `gt:1.2` | Theorem 1.2 (Clark two-node) | `clark_two_node_uncertainty`, `clark_two_node_equality_iff` (`SignUncertainty/ClarkTwoNode`) | formalised |
| `sr:window-pairing` | Lemma WP (`ft:WP`) | none | not formalised: FT-H4b of this plan (not in Paper I's plan) |
| `sr:WR` | Lemma WR (`ft:WR`) | none | not formalised: FT-H4b of this plan |
| `teb:quant_c1` | Proposition TE.0 | `teb_quant_c1_typeII` (`ConcreteBootstrap/QuantC1Airy`, imported by Paper I) | formalised (Airy, type II) |
| `teb:quant_c1_near` | Remark TE.0 flat (near threshold) | none | not formalised: FIVE-L (new file beside `QuantC1Airy`, which is not edited) |
| `teb:quant_c1_hb` | Proposition TE.0' | `teb_quant_c1_clark_typeII`, `_firstLevel` (Clark pair, `m_0 = 2`) | partial: general `(P,Q)` is Paper I's M8 |
| `teb:bootstrap` | Theorem TE.2 | `teb_bootstrap_part1`, `teb_bootstrap_part2`, `teb_bootstrap_part3`, `teb_bootstrap_hb`, `teb_mellin_o1_lower` (`TwoEdgeBootstrap/Bootstrap`) | formalised |
| `teb:kernel` | Lemma TE.1 | `stripPoisson_representation_symm` (`ModularBootstrap/StripBand/StripPoissonRep`, part (a)) | formalised (part (a)) |
| `teb:edge-osc` | Lemma TE.1a | `teb_edge_osc` (`TwoEdgeBootstrap/EdgeOsc`) | formalised |
| `teb:mellin` | Proposition TE.3 | `teb_band_reduction`, `teb_band_reduction_quantified` (`ModularBootstrap/StripBand/BandReduction`) | formalised |

## Appendix A. Label index

Every stated result of the paper and supplement, by file. Format: `label` (aliases) state, then the group of section 3.
Within a file, results are grouped by group and state. D done, P partial, PL planned, NP not planned, R recalled from Paper I.

**`blowup_limit.tex`** (6)
- D / BL: `bl:T`, `bl:T1`, `bl:T2`, `bl:T4`, `bl:T5`
- PL / BL: `bl:norm`

**`comb_estimates.tex`** (9)
- D / CMB: `cmb:K0`, `cmb:K1`, `cmb:K2`, `cmb:K3`, `cmb:K4`, `cmb:K5`, `cmb:K6`, `cmb:K7`, `cmb:K8`

**`constant_term_lower_log.tex`** (3)
- PL / FIVEL: `ctl:dyadic`, `ctl:pass2`, `ctl:freeze`

**`constant_term_slit_strip.tex`** (17)
- PL / FIVE0: `cts:langer`, `cts:phaselock`, `cts:involution`, `cts:main`
- PL / FIVEL: `cts:edge-hankel`, `cts:cauchy-dual`, `cts:rosc-uncond`, `cts:boas`, `cts:lower-main`
- PL / FIVEU: `cts:smooth-env`, `cts:tip-shared`, `cts:upper-design`, `cts:regionII-floor`, `cts:shifted-langer`, `pm:tip-match`, `cts:upper-vac`, `cts:transfer`

**`constant_term_universality.tex`** (8)
- PL / FIVEW: `ctu:main`, `ctu:table`, `ctu:weight`, `ctu:strip`
- P / FIVEW: `ctu:O1` (`ctu:Airy`, `ctu:c0`)
- PL / FIVE0: `ctu:piece4`, `ctu:jets`, `ctu:common-functional`

**`crossing_sum_rule.tex`** (3)
- D / CR: `fw:abel`, `fw:crossing`, `fw:FWC`

**`dual_spectrum.tex`** (7)
- D / DU: `ds:D1`, `ds:M`
- P / DU: `ds:farkas`, `ds:E`, `ds:E1`
- PL / PA: `ds:primal`
- PL / LP: `ds:LP`

**`dual_spectrum_limit.tex`** (7)
- PL / LP: `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact`
- PL / PA: `dsl:strip-fixed`, `dsl:one-level-clusters`, `dsl:near-opt-mass`

**`edge_transform_sd.tex`** (6)
- D / ESD: `esd:asym`, `esd:hankel`, `esd:global`, `esd:phase`, `esd:lemmap`, `esd:lemma`

**`integrality.tex`** (11)
- PL / INT: `int:sonine`, `int:cheb`, `int:repair`, `int:shell-inv`, `int:atom`, `int:reserve`, `int:hb-reserve`, `int:strict-weak`, `int:main`, `int:int-closed`, `int:obstr`

**`integrality_lattice.tex`** (5)
- NP / INTL: `int:lat-reserve`, `int:poinc`, `int:amgm-floor`, `int:lat-repair`, `int:int-spin`

**`integrality_spin.tex`** (4)
- PL / INTS: `int:axis-trace`, `int:cheb2d`, `int:cos2d-repair`, `int:cont-spin`

**`lower_o1_two_edge.tex`** (27)
- D / LB1: `vlo:Bessel`, `vlo:Gap`, `vlo:PJ`
- P / LB1: `vlo:BesselConst`
- D / LB3: `ft:PP` (`wone:Q`), `vlo:J` (`int:Jslack`)
- D / LB2: `vlo:S1` (`wone:transfer`), `vlo:S2`, `vlo:S3`, `vlo:S4`, `vlo:S5`, `vlo:S6`, `vlo:XV`, `vlo:J40`, `vlo:J41`, `vlo:J42`, `vlo:YV`, `vlo:E2`, `vlo:F`, `vlo:Zp`, `vlo:J7Q`, `vlo:Dp`, `vlo:Z`, `vlo:L`, `vlo:J10escape`
- P / LB3: `wone:ftlfw`, `wone:genlower`

**`n1_super_virasoro.tex`** (5)
- NP / W: `n1:P1`
- D / W: `n1:L2`, `n1:L4` (`wone:weightlem`)
- P / W: `n1:T3`, `n1:T5`

**`positive_mixtures.tex`** (14)
- PL / PM: `pmix:main`, `pmix:rebase`, `pmix:weight`, `pmix:crossing`, `pmix:punif`, `pmix:ramped`, `pmix:smooth`, `pmix:o1`, `pmix:duality`, `pmix:vac`, `pmix:hbphase`, `pmix:hbtap`, `pmix:rigidity`, `pmix:jets`

**`recalled_paper1.tex`** (22)
- R / REC: `ap:thmD` (`thm:airy-defect`), `ap:corD1`, `ap:lemH`, `ap:lemFR`, `ap:lemHp`, `ap:thmQ` (`thm:airy-quadrature`), `lam:thmB` (`ap:thmB`, `thm:airy-threshold`), `gt:1.0`, `gt:1.0p` (`lem:hb-good-circles`), `gt:1.0pp` (`lem:hb-quadrature`), `gt:1.1` (`cor:clark-quadrature`), `lem:hb-uniqueness`, `gt:1.2` (`thm:clark-threshold`), `sr:window-pairing`, `sr:WR`, `teb:quant_c1` (`prop:airy-local-stability`), `teb:quant_c1_near`, `teb:quant_c1_hb` (`prop:hb-local-stability`), `teb:bootstrap` (`thm:strip-feedback`), `teb:kernel` (`lem:strip-poisson`), `teb:edge-osc`, `teb:mellin` (`prop:mellin-feedback`)

**`remainder.tex`** (9)
- D / CMB: `rem:P1.1`, `rem:P1.2`, `rem:analytictip`, `rem:analyticII`, `rem:cardy`
- PL / STAB: `rem:thmBstab`, `rem:thmOloc`
- D / STAB: `rem:thmL`
- P / STAB: `rem:corL`

**`rigidity.tex`** (1)
- D / RG: `rig:R`

**`soft_edge_two_level_stability.tex`** (5)
- PL / TL: `se:terminal-stability`, `se:3.1`, `se:3.3`
- D / TL: `se:3.2`
- P / TL: `se:cdual`

**`spectral_rigidity.tex`** (5)
- P / SR: `sr:P`, `sr:Sigma0`, `sr:Sigma`
- PL / SR: `sr:cor`, `sr:single-level`

**`spinning_calibration.tex`** (2)
- PL / SPINF: `scal:C1`, `scal:C3`

**`spinning_dual.tex`** (9)
- PL / SPIND: `sd:M`, `sd:T`, `sd:P`, `sd:SD`, `sd:W`, `sd:V`, `sd:A`, `sd:LP`, `sd:R`

**`spinning_foundations.tex`** (7)
- PL / SPINF: `spinnotes:S1`, `spinnotes:S21`, `spinnotes:S22`, `spinnotes:S22b`, `spinnotes:S23`, `spinnotes:S24`, `spinnotes:S3`

**`spinning_integer_exact_slope.tex`** (5)
- PL / SPINZ: `spinnotes:K1`, `spinnotes:K2`, `spinnotes:K3`, `spinnotes:K4`, `spinnotes:K4a`

**`spinning_integer_liouville.tex`** (11)
- PL / SPINZ: `spinnotes:L0a`, `spinnotes:L0b`, `spinnotes:L1`, `spinnotes:L2`, `spinnotes:L3`, `spinnotes:L4`, `spinnotes:L5`, `spinnotes:L6`, `spinnotes:L7`, `spinnotes:L8`, `spinnotes:L9`

**`spinning_integer_overview.tex`** (2)
- PL / SPINZ: `isl:main`, `isl:finite`

**`spinning_s4.tex`** (14)
- PL / SPIN4: `s4:S4`, `s4:2.1`, `s4:2.2`, `s4:2.3`, `s4:2.4`, `s4:3.3`, `s4:3.4`, `s4:4.1`, `s4:4.2`, `s4:4.3`, `s4:5.1`, `s4:5.2`, `s4:6.1`, `s4:4.4`

**`upper_transfer.tex`** (20)
- D / UTW: `ut:Z`, `ut:P`, `ut:Phi`, `fw:FWM`, `fw:SDp`, `ut:W`, `ut:ID`, `ut:G`, `ut:V` (`uc:V`), `ut:E`
- D / UTP: `ut:II`, `ut:R`
- P / UTP: `ut:IIF`, `ut:I`, `ut:III`, `ut:T`, `ut:Vac`
- P / T2: `ut:ideal`, `ut:T2`, `wone:clark`

**`virasoro_two_level.tex`** (3)
- P / TL: `gt:hb`, `gt:2.4` (`gt:2.5`, `gt:2.6`)
- D / TL: `gt:2.1`

**`modular_bootstrap_gap_proof.tex`** (2)
- PL / FIVEW: `thm:fixed-weight-expansion`, `thm:spinless-expansion`

Totals: 249 results; done 72, partial 24, planned 125, not planned 6, recalled from Paper I 22.

## Appendix B. Calibration (lines of Lean under `FormalResearch/ModularBootstrap/`, `master` `5b7fa76`)

| directory | lines | directory | lines |
|---|---|---|---|
| `Upper/` (Ramped 18.9k, Window 14.8k, Holes 11.1k, Comb 10.6k, Saddle 8.6k, Hankel 4.8k, Assembly 4.2k, Rigidity 3.7k, Membership 3.6k, Positivity 3.9k, Design 3.5k, Bump 2.3k) | 89.9k | `FixedWeightBand/` (55 files) | 19.4k |
| `TwoLevel/` (73 files; `TwoZero*` 5.6k, `ClarkRigidity*` 3.3k) | 15.2k | `Contour/` | 12.5k |
| `ConcreteBootstrap/` | 11.4k | `Crossing/` | 7.5k |
| `PoissonJensen/` | 7.2k | `FixedWeightTip/` | 6.7k |
| `ChartGeometry/` | 6.4k | `Chart/` | 6.3k |
| `Blowup/` | 5.7k | `WeightAxioms/` | 5.4k |
| `SlitStrip/` | 4.7k | `StripMultiplier/` | 3.8k |
| `StripBand/` | 3.6k | `ComplexBessel/` | 2.9k |
| `FixedWeight/` | 2.9k | `TipFront/` | 2.7k |
| `Duality/` | 2.4k | `FoldTip/` | 2.3k |
| `Bessel/` | 2.0k | `Rigidity/` | 1.4k |
| `Mellin/` | 1.0k | `Integration/` | 0.5k |
| `Constants.lean` | 0.35k | total `ModularBootstrap/` | 224k |

Other: `TwoEdgeBootstrap/` 4.0k, `Special/Airy*` 47.9k (Paper I).
