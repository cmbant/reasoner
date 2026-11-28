# Paper II (modular bootstrap at large c) — Lean plan

**Source.** QIprojects `CFT/modular_bootstrap/paper/` at `origin/main` `80acaed64` (2026-11-27; after PR 307 it includes PR 309
(Theorem SD-M2), PR 311 (integer-spin Part L), PR 312 (Lemma FJ), PR 313 (log-free lower remainders) and the editorial trims).
Master file `airy_scale_core.tex`, supplement `modular_bootstrap_supplement.tex`; Lemma U* is in the note
`CFT/notes/n2_ramped_comb.tex`. Three lemmas used by the five-term proofs of both papers are printed once, in the Paper I
supplement, from `CFT/common/`: FS.1 `fs:half-cubic` (signed CFU pairing, `fine_order_signed.tex`), FS.2 `fs:circle` (two-moment
good circle, `fine_order_circle.tex`), FJ `fj:lemma` (fine-order fold reduction, `fine_order_fold.tex`). Theorem FQ (`fq:main`,
`CFT/notes/five_term_quantisation.tex`) is the notes-level coefficient dictionary for both papers. Section 5.3 lists what changed for
Lean since the previous audit (`0932a6c6f`).

**Lean.** reasoner `master` (INT-4, PA1 at every fixed charge, multilevel `se:terminal-stability`, `dsl:one-level-clusters` at `(H_w)`, PM-2 consumer ports, `pmix:o1` comparison, `cts:edge-hankel` (2), PM-4, `scal:C1`/`C3`, `spinnotes:S1` (a, d, e); FT-CC with its Hankel
and fixed-weight instances; `IntRepairSonineInput` discharged, so `int:atom` is unconditional; all fourteen `s4:*` results
(`spinS4`); `sr:cor` barycentre, offset form of `se:3.3`, `s`-variable form of `bl:norm`). No lane is running; every open package
is unstaffed. Umbrella `FormalResearch.ModularBootstrap`;
declaration map: `THEOREM_MAP.md` (section "Modular Bootstrap" and the `Upper/`, `FoldTip/`, `TwoLevel/` sections after it);
reader-facing status: the Paper II section of QIprojects `docs/lean_status.md`.

This file says what is true now; git holds its history. Nothing is claimed formalised that is not on `master`, and a `.lean` file
existing is not verification. Under `FormalResearch/ModularBootstrap/` there is no proof placeholder, no `axiom` and no
`native_decide`; every headline named here has a `#guard_msgs` / `#print axioms` guard pinning `[propext, Classical.choice,
Quot.sound]`.

## Best next steps (prioritised; the smallest first concrete step of each)

1. **Five-term lower, restate `LowerMainInputs` one-pass and log-free (S, a few hundred lines; `FiveTerm/LowerMain*`).** Since PR
   313 Theorem C9 is `-C_- c'^{-1}` and its proof has one pass. New fields: `combined` = C7(4) at every good radius,
   `|P_R(H) + g_vac/2pi + band| <= C (c^{-1} eta_R + c^{-4/3})` (no `1_{E_un}` term, no pass-1 conjunct); `pass2` = C7b, unconditional
   (some good `R` in the range with `eta(R) <= C c^{-1/3}`); `boas` = C8, `band >= -C c^{-4/3}`; `chart` unchanged. Delete
   `LowerPassOne` and the two-pass `lower_pass_upper`; `lowerUstar` loses its `log c`; `spinless_lower_of_inputs` then gives the
   first display of `cts:lower-main` (`-C c'^{-1}`) modulo the fields. The current (log, two-pass) fields follow from the new ones,
   so nothing proved is lost. First step: rewrite the four `Prop`s in `LowerMain.lean`.
2. **Five-term lower field `pass2` (C7b via FS.2; M).** The mechanism is already in Lean: Paper I's `CtDyadicRadius.ct_dyadic_radius`
   (two Cauchy moments, `CtDyadicArea.ct_area_of_zeta`, `Complex/HalfDiscMoments`, Markov selection on Paper II's `lowerGoodSet`,
   `airy_eta_le_arcs`), and Paper II's `LowerGoodArea`, `LowerGoodWtilde`. First step: state FS.2 phase-free (arc mass `<= C/A`,
   absolute second moment `<= C A`, chart `I_n(u) - u = O(n^{-1/3})`, `I_n' = 1 + O(n^{-1})`) in a shared file and re-derive
   `ct_dyadic_radius` from it (Paper I owns the file; agree in both plans). Then the Virasoro instance needs only top-scale inputs:
   `ctl:cov` on `|u~| = R_J` with Lemma Q(2) on the wedges, and `B_1(R_J) + B_2(R_J) <= C c'^{-1/3}` (Propositions L and X_V:
   `virasoro_band_sums_le`, `YVEnvBound`). *Check:* does `YVEnvBound` at `R = A^2` give `ctl:cov` at the top scale (Paper I's
   analogue is `CtBandData`)? FS.1 is also in Lean (step 5) and is the tool wherever the proof pairs signed CFU terms. The
   multiscale bootstrap and the half-moment `ctl:half` are not on this path.
3. **Five-term lower field `chart` (M-L).** (a) Lemma FJ (2), generic: inverse of `J_n(u) = u + 2^{-2/3} n^{-1/3} psi_n(2^{2/3} n^{-2/3} u)`
   on a scaled disc, its expansion, derivative bounds and the five-term transport formula (Rouché/injectivity, pure complex
   analysis; shared with Paper I, whose `ct_chart_complex`, `CtChartPsiAnalytic`, `HankelChartCubic` do the Hankel case by hand).
   With it `LowerChart` reduces to: `psi_eps` real-symmetric, holomorphic and bounded on a fixed disc with `psi_eps(0) = beta_eps`,
   `psi_eps'(0) = gamma_0 + O(eps)`. (b) That statement for the Virasoro odd phase is FJ (1) applied through the CFU chart
   (`cts:cauchy-dual` Steps 3-4; reuse `CtCfu*`, `FctCfuTheta.cfu_chart`, `CtSd*`). First step: (a).
4. **Five-term upper (unchanged by the update).** C14 `cts:upper-vac` (2-4k) first, then C12, C13, C11 (section 1.1).
5. **Five-term lower fields `boas` (C8 with the averaged freezing C8a) and `combined` (C7(4) with FS.1).** FS.1 is in Lean (Paper I's
   `SignUncertainty/FineOrderSigned*.lean`: `fs_principal`, `fs_aux`, `fs_pairing_principal`, `fs_pairing_aux`; phase-free, it also
   gives Paper I its log-free `thm:ct-lower`), so `combined` consumes it rather than re-proving it. First step: *check* that
   `HalfCubicData` accepts the analytic weights `-V_1/(1-e^{-4 pi x})^2`, `3/(16 pi x)` of `cts:Kedge-signed`, then instantiate
   `fs_pairing_principal` and `fs_pairing_aux` for them.
6. **Universality:** PM-0b (jets at general amplitude), FT-H4b, then INT-2, INT-S (headline 1); `pmix:liminf` needs the component `c_0^*(w,Q_i)` lower bounds (FIVE-W `ctu:c0`, `int:strict-weak`).

**Where things stand.**
- *Lower and upper `O(1)` law, every integer `(w,Q)`:* `Delta_best = c'/Lambda_V + A_opt c'^{1/3} + O(1)` two-sided, no hypothesis
  (`fixedWeightLowerBoundInput_of_problem`, `theoremC15UpperInput_probW`); the design side (Proposition V, Lemma T, Property (P),
  `Sigma_0`, `Sigma`), the fold-tip instances and Corollary 2.4(a) at every weight; T2, Theorems 2.5, 2.6, `wone:clark`(c) and
  `se:3.3` (zero and compact offsets) at every weight for the two-zero designs `(f,r) = (2,1)`; the `sr:cor` barycentre and the
  `s`-variable form of `bl:norm` for any `HermiteBiehlerData`.
- *Duality:* `ds:E` (a), (b) compact `F`, (c) at every `(w,Q)`; `ds:primal` (`theorem_primal`) and `dsl:strip-fixed`(a) (`dsl_strip_fixed_a`) at every
  fixed charge `0 < c~`, `12 S <= c~`, no strip hypothesis; Theorem LP (`ds:LP` (i)-(iii) at `(H_w)`) with `ds:cay`, `ds:cont`, `ds:mom`,
  `dsl:poly-compact`; PM-4 for common sources and mixtures at every fixed charge in range; `se:cdual` (all six declarations)
  unconditional at every fixed charge; `se:terminal-stability` (all clauses, fixed strict HB data); `dsl:one-level-clusters`
  (a), (b) and `dsl:near-opt-mass`/`dsl:D1-exact`/`dsl:d1-asym` at `(H_w)`.
- *Five-term expansion (headline 3):* all Virasoro constants are read off the outer function (`c0Star`, `gamma0`, `d2Star`); both
  halves of `thm:spinless-expansion` are proved **modulo named input structures** (`UpperMainInputs`: fields C11-C14;
  `LowerMainInputs`: `chart`, `combined`, `pass2`, `boas`). The Lean lower half has `-C c'^{-1} log c'`, which matches
  `thm:spinless-expansion` as stated but is weaker than `cts:lower-main`, `cts:transfer`, `ctu:main` since PR 313 (step 1 above).
- *Spin (headline 1):* SPIN-F complete (`spinS3` unconditional); eight `sd:*` labels done (`sd:spinmoment` unconditional), `sd:R` partial (needs `dsl:hb-mass`);
  all fourteen `s4:*` results proved (`spinS4_4_4`, `spinS4` unconditional); integer spin (SPIN-Z) not started;
  integrality: INT-T tools including `int:repair` and `int:sonine` at integer weights (`hankel_repair`, `hankelSonine_inv`), INT-4 at
  `(H_w)`, `int:atom` unconditional.
- *Mixtures (headline 4):* PM-0, PM-1, PM-2 to stated scopes (partial), PM-4 done at every fixed charge in range; `pmix:o1` two-sided for every common source (`pmix_o1_common`) with the component comparison (`pmix_o1_component_comparison_unconditional`); PM-2 consumer ports and `pmix:rigidity` (a), and (b) at zero offset (`src_sigma_unconditional`, `src_two_level_exclusion`, `src_theorem_two_six`); `pmix:liminf` conditional on component `c_0^*` lower bounds (`pmix_liminf_of_component_c0`); FT-CC done with its Hankel-prescribed and fixed-weight instances (`hankelPrescribed_chartCompactness`,
  `fixedWeight_chartCompactness`); `shellReduction_littleO` gives the `o(d^{1/3})` shell reduction at all levels (Paper I's `O(1)`
  `ShellReduction` still needs M8's all-level `teb_mellin` / `teb_bootstrap_hb`).

**Counts** (counted from Appendix A against the TeX at `80acaed64`). 264 stated results: 261 `result` environments, the
`theorem` and `corollary` of `modular_bootstrap_gap_proof.tex`, and Lemma A_V (`rem:cardy`, a `remarkx`); several labels on one
result are one row. State on `master`: **125 done, 51 partial, 59 planned, 6 not planned, 23 recalled from Paper I**
(22 in `recalled_paper1.tex`, mapped in 7.10, and `dsl:compact-mass`). Appendix A has every label. Changes since `0932a6c6f`:
`spinnotes:K3` left the paper (now in the note `notes/tex/spinning_integer_alternative_proofs.tex`); new `sd:spinmoment`,
`spinnotes:L3a`, `spinnotes:L8a` (planned); `cts:rosc-uncond` partial -> planned (Lean's `eta(R_1) <= C` is no longer part of
its statement, see 5.3).

*Counting rule.* A label moves only when its row says so and its whole statement changes class. A general-`m` or general-factor
part still open, a statement proved in a different variable, or one proved under a hypothesis the paper omits keeps it partial or
planned; a proved proof step that is not part of the statement moves nothing (`cts:boas` Step 3, `ctu:jets` at Virasoro,
`ctl:dyadic`/`ctl:pass2`/`ctl:freeze` exponent bookkeeping, `lowerFirstGood_of_chart_on_band`). Calls that need the rule spelled out:
- *Partial, modulo a named hypothesis:* `cts:transfer`, `thm:spinless-expansion`, `cts:lower-main` (first display only, and with the
  weaker `-C c'^{-1} log c'`); `pmix:rebase` (local finiteness of the push-forwards).
- *Partial, special case or weaker form:* `spinnotes:S1` (the `T`-invariance remark of (a) omitted); `ds:LP` (`(H_w)`
  only; the paper states the dominated class `(H_{w,lambda})`, mixtures are PM-4); `dsl:reserve` (the `d = 2` swap-invariant form
  `dslReserve` only); `cts:smooth-env` (all three parts at Virasoro; stated for general `(w,Q)` outer functions);
  `cts:edge-hankel` ((1) and (2) at Virasoro via `LowerEdgeHankel` and `LowerEdgeAsymp`; `G` is the defined Hankel integral);
  `ctu:common-functional` (Virasoro data); `cts:involution` (weaker endpoint bound near `+-i`); `bl:norm` (`u`- and `s`-variable; node data a hypothesis at general `(P,Q)`);
  `pmix:smooth` (coefficient `1/2` for the paper's `3/8`); `pmix:vac` (`(1,0)`, `(2,1)`, one-sided limit); `pmix:punif`,
  `pmix:ramped`, `pmix:o1`, `pmix:weight`, `pmix:crossing`, `pmix:jets`, `int:repair`, `int:sonine` (integer weights `w >= 1`;
  Lean's constants differ from the paper's), `int:obstr` ((a) at `(H_w)`), `se:3.3`, `sr:cor`, `ds:farkas`, `ds:E1`,
  `dsl:strip-fixed` (evenness of `G` and analyticity of `g` on `(-a',inf)` not stated), `ds:primal` (analyticity clause and class `(H_{w,lambda})`), `dsl:one-level-clusters`, `dsl:near-opt-mass` (`(H_w)` only; mixtures and dominated sources not ported), `pmix:duality` (see `ds:primal`), `pmix:rigidity` ((a); (b) at zero offset), `rem:corL`, `sd:R` (`spinDR` proves the Airy law of the dimension marginals; the
  `dsl:hb-mass` concentration bounds are not in Lean), `sr:P`,
  `sr:Sigma0`, `sr:Sigma`, `ctu:O1`, `ut:ideal`, `ut:IIF`, `ut:I`, `ut:III`, `ut:Vac`, `gt:2.4`-`gt:2.6` (the missing part is named
  in each row).
- *Planned although Lean has a related object or step:* `ctu:jets`, `ctu:piece4` (Virasoro jets only); `int:cheb` (Lean
  has the floor `8 N^{5/2}` of `int:cheb-explicit`, not `640 N^2`); `cts:boas` (Step 3 core only); `cts:rosc-uncond` (Lean has
  `eta(R_1) <= C` at a first good radius modulo `chart`, weaker than (1)'s `eta(R) <= C c'^{-1/3}`).
- *Done although proved in a different form:* `cts:langer` (`lowerLangerPhase_holds` links the chart to the comb phase on the real
  band); `cts:main` (Virasoro data; the decimal `-0.0713...` is numerical); `cts:tip-shared` (every part, `cts:BC-id` under the
  corrected TeX hypotheses).
- *Recalled, with a Paper II Lean proof of the case used:* `dsl:compact-mass` (recalled from Paper I `lem:qual-compact`, which is
  in Lean as `Analysis.qual_compact`; Paper II's `compact_negative_mass` is the uniform-convergence case used by
  `dual_spectrum_limit.tex`).

## 0. Vocabulary

- **State.** *done*: the paper's statement, in the paper's scope, is a Lean theorem with pinned axioms. *partial*: Lean proves a
  special case (Virasoro, integer `w`, `w = 1`, two-level `F = {t_1}`, ...) or part of the statement, or proves it modulo a named
  hypothesis; the row says which. *planned*: a work package owns it. *not planned*: reason given.
- **Proved modulo X**: the theorem has hypothesis X (a structure or `Prop`) that is not itself proved on `master`. **Stated**: a
  definition or statement exists without proof. These words are used in that sense only.
- **Size** (lines of Lean): S < 500, M 500-2000, L > 2000. Calibration in Appendix B.
- **`(H_w)`**: integer weight `w >= 1`, null factor `Q = prod (1 - q^{mu_l})`, `mu_l > 0` (Lean `FixedWeightProblem`);
  `(H_{w,mix})`: positive finite mixtures of shifted products; `(H_{w,lambda})`: uniformly dominated thermal sources
  (`pmix:dominated`). Lean `ShiftSource` with `FloorData` (`CommonSource`, PM-0) is the dominated class for finitely atomic
  `lambda` (signed coefficients allowed); general measures `lambda` are not formalised.

External Lean code that may serve both papers: `FormalResearch/CFT_REUSE.md`.

## 1. The four headline results

The introduction of `airy_scale_core.tex` states four results. Rows are ordered by critical-path length, longest first ("#" is
the paper's number). Package details are in section 2.

| # | headline (paper) | Lean today, compared with the paper | path from master |
|---|---|---|---|
| **3** | **Five-term expansion** `thm:fixed-weight-expansion`, `thm:spinless-expansion`: `Delta_best = c'/Lambda_V + A_opt c'^{1/3} + c_0^* + c_1^Langer c'^{-1/3} + d_2^* c'^{-2/3} + E`, `-C_- c'^{-1} log c' <= E <= C_+ c'^{-1} log c'` (the supplement's `cts:transfer`, `ctu:main` and the main text have the sharper `-C_- c'^{-1}` below) | **Weaker.** `O(1)` law at every `(w,Q)`. Virasoro constants complete (FIVE-0). Virasoro expansion proved modulo `UpperMainInputs` (`spinless_upper_of_inputs`) and `LowerMainInputs` (`spinless_lower_of_inputs`, log lower remainder); satisfiability of neither structure is checked. Nothing at general `(w,Q)` | FIVE-L restatement and fields, FIVE-U fields, then FIVE-W |
| **2** | **Extremal spectrum**: attainment and atomicity (`ds:primal`), Airy clusters (`sr:Sigma`, `sr:cor`, `sr:single-level`), Clark curve (`gt:2.1`, `gt:2.4`-`gt:2.6`) | **Weaker or special.** `Sigma_0`, `Sigma` for the extremal measures at every weight (paper: any measure satisfying `Gap`); `gt:2.1` matches; `gt:2.5`, `gt:2.6`, `ut:T2`, `wone:clark`(c) at every weight for two-zero designs; `ds:E` done; `ds:primal` and `dsl:strip-fixed`(a) at every fixed charge `12 S <= c~`; `sr:cor` cluster masses, positions and barycentre; `se:3.1` both assertions; `se:cdual` and `se:terminal-stability` (multilevel) done; `dsl:one-level-clusters` and `dsl:near-opt-mass` at `(H_w)`; nothing for `sr:single-level` | PA2 rest (`sr:single-level` and the exact first atom need FIVE-W `ctu:main`; mixture and HB forms) |
| **4** | **Universality across chiral algebras**: fixed weight (`n1:T5`), `N = 1` (`n1:T3`), positive mixtures (`pmix:main`), prescribed HB levels (`gt:hb`) | **Partly.** `O(1)` law and duality at every `(w,Q)`, `N = 1`; PM-4 duality for sources and mixtures; `bl:norm` for any `HermiteBiehlerData` (`hb_blnorm`, `hb_blnorm_s`); stability slopes (`se:3.1`, `se:terminal-stability`); `pmix:o1` two-sided for every common source with the component comparison; mixtures PM-0..PM-2 partial; `pmix:rigidity` (a) and the zero-offset part of (b) for `CommonSource`; FT-CC with its Hankel-prescribed and fixed-weight instances. Five-term, general HB levels: none | PM-0b, FT-H4b, `pmix:liminf` (needs FIVE-W `ctu:c0`), then PA2 rest, PM-3, INT-2HB, HB1, PM-5; five-term at `(w,Q)` via FIVE-W |
| **1** | **Spin does not help**: continuous spin (`s4:S4`, `spinnotes:S3`, `sd:R`, `sd:spinmoment`), integer spin (`isl:main`, `spinnotes:L8a`), finite-order programmes (`isl:finite`); integrality shifts the spinless optimum exponentially little (`int:main`) and by `O(log c')` with continuous spin (`int:cont-spin`) | **Partly.** `spinnotes:S3` unconditional (`spinS3`: `(c-1)/Lambda_V - C (c-1)^{1/3} log(c-1)^{2/3} <= Delta_L <= Delta_spin <= Delta_best <= (c-1)/Lambda_V + A_opt (c-1)^{1/3} + C_+`); `sd:*` done except the `dsl:hb-mass` clause of `sd:R`; `s4:S4` and all `s4:*` unconditional (`spinS4`); `int:obstr`(a), `int:atom` unconditional (with `int:repair`, `int:sonine` at integer weights). `sd:spinmoment` (SD-M2) unconditional (`spinMoment_vagueLimit`, `spinMoment_cluster_ratio_tendsto`, `spinMoment_endpoint_tendsto`, `spinMoment_pair`). Integer spin and `int:main`: none | INT-S, SPIN-Z; INT-2, INT-3 |

### 1.1 Next steps per headline, smallest first

Each step names its inputs. "Check" marks a question to settle before writing Lean.

**Headline 3 (five-term).** The remaining work is the analytic estimates behind the two input structures. Since PR 313 the lower
side is shorter: one good circle (C7b, top-scale inputs only), signed CFU pairing (FS.1) and averaged Boas freezing (C8a); the
multiscale dyadic bootstrap `ctl:dyadic` (beyond its top scale) and the half-moment `ctl:half` are no longer on the headline path.
1. *Reuse audit (S, done in `FiveTerm/FIVEL_DESIGN.md` §7 and `FiveTerm/FIVEU_DESIGN.md` §7, against the TeX before PR 313).*
   Phase-free Paper I machinery is directly reusable (`CtDualId`, `CtRoscUpper`, `CtRoscEta`, `CtRoscDefect`, `CtBoasAverage`,
   `CtBoasTent`, `CtBoasFreeze`, `CtBoasAssembly`, `CtChartIft`, `CtChartInverse`, `CtSdEval`, `FctCfuTheta.cfu_chart`,
   `CtDyadicArea`, `CtDyadicRadius`, `HalfDiscMoments`); no `LowerMainInputs` or `UpperMainInputs` field follows from Paper I
   without new Virasoro-phase proofs. Paper I's `CtLowerFinal.ct_lower` (master `1e8e81d`) is unconditional in the old
   `-C c^{-1} log c` form (absolute half-moment `hankel_neg_half_moment_le`, pointwise CFU); its TeX is now log-free too (R560).
2. *FIVE-L restatement (S):* Best next step 1.
3. *FIVE-L field `pass2` (C7b, M):* Best next step 2 (FS.1 is available in Lean).
4. *FIVE-L field `chart` (`cts:cauchy-dual` (1) with `cts:phic-exp`, C6; M-L):* Best next step 3. Since PR 313 `cts:phic-exp` is
   derived in the TeX from FJ (2), and the saddle shift `psi_eps` from FJ (1).
5. *FIVE-U C14 `cts:upper-vac` (2-4k):* vacuum sum over the Airy window and band, `x_split` cancelling, `tip_match` as input; the
   field `c14_vacuum` (`cts:Vc-exp`).
6. *FIVE-L field `boas` (C8, M):* Step 3 is `LowerBoasResidue`; Steps 1-2 follow the Gaussian-window route with the
   centre-averaged freezing of C8a (`ctl:freeze`: replacing `P`, `W~_eps`, `theta~_eps` by their centre values changes the
   centre-averaged integral by `O(c'^{-4/3})`, using the derivative bounds `ctl:freeze-derivatives` and `ctl:dyad` at `R`).
   Gaussian-window exponents are in `LowerDyadic`; Paper I's `ct:boas` route (`CtFejer`, `CtBoasFreeze`) is the template.
7. *FIVE-U C12 `cts:regionII-floor` (4-6k):* hole comparison, Euler product for pairs `k = n +- m`, monotonicity of
   `|T_{chi+i eps}|^2` in `eps` (reuse `Upper/Comb/Factors.blaschkePairQ_mono_eps`, `Upper/Bump/PairFactor`), trigonometric
   phase-error positivity, `C_buf = 4(C1+C2)+1`; builds on `Upper/Holes` K4-K6. Field `c12_regionII`.
8. *FIVE-L field `combined` (C7(4), M-L):* the dual identity with coefficient one, the residual decomposition
   `cts:combined-residual`, the signed CFU estimate `cts:Kedge-signed` (FS.1 (1)-(3) with analytic weights `-V_1/(1-e^{-4 pi x})^2`,
   `3/(16 pi x)`), `cts:D-orth`, the `E_c` exponential comparison on the upper half-disc, the outer band `c'^{-1} B_2(R') =
   O(c'^{-4/3})`. Depends on `chart`, Theorem D and the quadrature in `ConcreteBootstrap`. FS.1 is in Lean (step 5 of the best next steps: `fs_pairing_principal`, `fs_pairing_aux`).
9. *FIVE-U C13 `cts:shifted-langer` (5-8k):* exact-CFU shifted Langer identity with the global tip kernel, the `W_D^tip` bounds,
   `Pi_n` asymptotics, a good Airy radius, Region-I positivity; instantiate Paper I's divided-difference chart
   (`FctCfuTheta.cfu_chart`, `FctHomotopy*`, `FctJCBound`, `FctWeighted`), not a second CFU stack. Field `c13_regionI`.
10. *FIVE-U C11 `cts:upper-design` (6-10k):* needs K7 with an amplitude/envelope: `InnerCombHyp` demands `|B| <= 1` and `|B| = 1`
    on `E_+`, which `E_delta B_D` does not satisfy, so write amplitude-carrying copies of `Upper/Membership`, `Saddle`, `Hankel`
    (not in place). Fields `c11_membership`, `c11_first_site`.
11. *FIVE-W (5-8k if FIVE-L/U stay stated over general data):* `ctu:main`, `ctu:O1` (`c_0^*(w,Q)` clauses), `ctu:table`,
    `ctu:weight`, `ctu:strip`, `ctu:tip-window`, `ctu:tip-kernel`, `thm:fixed-weight-expansion`. FIVE-U is already stated over
    any `ShiftSource` and `OuterDatum`; check how much of FIVE-L's `LowerMainInputs` is Virasoro-specific before starting (since
    PR 313 the `ctu` lower side is FJ (2) with the C9 dictionary plus FS.1 with the analytic weights `a_2^{(w,Q)}`, `1/x'`).

**Headline 2 (extremal spectrum).**
1. *PA2 rest (M-L):* `dsl:one-level-clusters` (a), (b) and `dsl:near-opt-mass`/`dsl:D1-exact`/`dsl:d1-asym` are in Lean for `(H_w)` only
   (`one_level_clusters`, `one_level_near_opt_mass`); mixture and dominated cases not ported. `b_n = T_V - T_*` is proved `O(1)`, not
   identified with `c_0^*(w,Q)` (the exact first atom and `sr:single-level` need FIVE-W `ctu:main`). HB forms need PM-3.
2. *Residual PA1 items (S):* evenness of `G` and real-analyticity of `g` on `(-a',inf)` (`dsl:strip-fixed`(a)); `dsl:strip-fixed`(b) is
   `T_V_pos` (positivity only); local-holomorphic convergence of `G_j` is not exported.

**Headline 4 (universality).**
1. *`pmix:liminf` (M):* `pmix_o1_common` is the two-sided law for every common source and weakly feasible `T`; the component comparison
   is `pmix_o1_component_comparison_unconditional` (`0 < c`, `12 Smax <= c`; `pmix_o1_component_strict_gt` is a Lean addition) and
   `pmix_liminf_of_component_c0` gives `pmix:liminf` conditional on component lower bounds `hcomp`. Not in Lean: those bounds as
   `c_0^*(w,Q_i)` (via `ctu:c0`, `int:strict-weak`); needs FIVE-W. `ft_commonSource_twoEdge` is the one-level case
   `(P,Q) = (1,0)` of `wone:ftlfw` with zero vacuum slack; the slack form of `wone:ftlfw` does not give the signed-source lower half
   directly (`V_src/V_{Q_0}` need not be monotone), so the lower half reruns the fixed-weight chain over `CommonSource`.
2. *PM-0b (M, 2-3k):* `ctu:jets` at a general amplitude, hence `pmix:jets` (the input of `pmix:main` through `ctu:c0`).
3. *`pmix:rigidity` rest (M):* (a) and (b) at zero offset are in Lean for `CommonSource` (`Mixtures/SourceRigidity`, `SourceTwoLevel`).
   Not formalised: `D_2` lower bound, positive-mass existence for `A_2 < A_2^*`, offset `R_off`, `pmix:D1` log asymptotic, rebase
   transfer to the original `n`; (c) is PM-3.
4. *FT-H4b (M-L)*, then PA2 (HB forms), PM-3, INT-2HB, HB1, PM-5 in that order (section 2.3).

**Headline 1 (spin, integrality).**
1. *INT-2 `int:reserve`, `int:strict-weak` (M-L) at `(H_w)`, lower half first:* in the TeX, INT-2 is the canonical case
   `m_0 = 1` of `int:hb-reserve`. Its lower bounds (a)-(c) at `m_0 = 1` use only `bl:norm`(b) (SLK: `airy_blnorm`, `u`-variable, or `airy_blnorm_s`, `s`-variable;
   the local `C^1` and `L^1` convergence used are conclusions of `hb_blnorm_s`), the `O(1)` law (`u_n(T) -> a_1`), `fw:crossing`(1) and `ds:E`(c) (`theorem_E_c_reserve`, with the variational
   formula `int:reserve-var`); state them as a `lower` conjunct. The matching upper bounds (the sharp law `int:hb-res-sharp`)
   need a fixed design transferred by `pmix:vac` (at `(H_w)`: the W-P5 design side), `ut:ideal`(a) for the `m_0 = 1` window
   family (check against Lean's `m = 2` `twoZeroIdealApprox`), and a weak extremal `g_*` from `ds:primal` with `g_*(B_n) = 0` and
   the cluster input `dsl:hb-clusters`/`dsl:one-level-clusters` (PA2); they are the `upper` conjunct. The mixture clause adds
   `pmix:rebase`, `pmix:o1`; the dominated-source clause waits for PM-5 (`pmix:dominated`).
2. *INT-3 `int:main` (M):* the integer-gap bound needs INT-1, INT-2 (lower half), INT-T, W-P6; the statement also has the
   cluster-mass equivalents in fixed Airy windows and the exponential concentration `|t - t^*_{k,n}| <= e^{-alpha n}`
   (`alpha < L(xi_*)` for `k = 1`, `< L(xi_*)/2` for `k > 1`), via `dsl:one-level-clusters`, `dsl:hb-mass` (PA2); the
   five-term corollary needs FIVE-W.
3. *INT-4 for mixtures/common sources (S-M):* PM-4 and PA1 are done at every fixed charge, so `int:obstr`(a) can be rerun over `SourceDualSetupCore`.
4. *SPIN-Z, INT-S* (SPIN-S4 is done; section 2.1).

## 2. Work packages

### 2.1 Open packages

Listed by headline. "Needs" names packages or labels whose Lean is not yet sufficient; done inputs are named where useful.

**FIVE-L** (headline 3; L, about 15-20k after PR 313, about 5k done). Closes `cts:edge-hankel`, `cts:cauchy-dual`,
`cts:rosc-uncond`, `cts:boas`, `cts:lower-main`, `ctl:pass2`, `ctl:freeze`, and (off the headline path since PR 313)
`ctl:dyadic` beyond its top scale; inputs `rem:corL`, `teb:quant_c1_near` (FIVE-W only), the shared lemmas FS.1, FS.2, FJ.
- *In Lean* (`FiveTerm/Lower*`, design `FiveTerm/FIVEL_DESIGN.md`): `corL_virasoro` (`rem:corL` at Virasoro: (a) type-II
  envelope, (b) via `quantC1B2_secant_lower`, (c) `QuantC1B2Holds`, (d) `u_T - a1 <= K c'^{-1/3}`, stronger than the paper's
  `c'^{-1/3} log c'`; the `C^1`-convergence clause of (c) is not exported; constants are Lean's `quantC1*`); `c0Star_neg`;
  `dimension_ge_of_phase_ge`, `delta_best_ge_of_phase`, `spinless_lower_of_phase` (modulo `LowerPhaseStatement`, gp:L);
  `edge_hankel_one_virasoro` (`cts:edge-hankel` (1)) and `edge_hankel_two_virasoro`, `besselV_three_term`,
  `besselI0C_two_term_sharp` (`cts:edge-hankel` (2), `LowerEdgeAsymp.lean`, unrestricted `v >= 0`; `G` is the defined Hankel
  integral, Hankel inversion is not formalised); `besselI0C_two_term`; `boas_residue_identity`, `boas_local_lower`,
  `boas_residue_zero`, `rect_boundary_zero` (`cts:boas` Step 3); `markov_select`, `dyadic_term_le`, `gauss_window_exponents`
  (bookkeeping; `pass2_exponents`, `top_edge_exponent` are the log-form exponents of the old two-pass proof);
  `lowerFirstGood_of_chart_on_band` (a first good radius with `eta(R_1) <= C`, modulo `chart`; since PR 313 a proof step of no
  TeX statement, kept as the template for C7b).
- *Skeleton (still the pre-PR-313 form):* `LowerMainInputs prob c0 gamma0` (data `Gout`, `phi`, `uhat`, `c1` with `0 < c1`,
  `10 c1 <= virasoroBVChoice`) over concrete objects (`lowerF`, `lowerH`, `lowerPNodes`, ...), fields `chart` (`cts:cauchy-dual`
  (1) + `cts:phic-exp`), `combined` (two-pass form of `cts:rosc-uncond` (4) with `c^{-4/3} log c` and the `c^{-1} 1_{E_un}` term),
  `pass2` (`eta <= C c^{-1/3} log c` under the pass-1 hypothesis `LowerPassOne`), `boas` (`>= -C c^{-4/3} log c`); fields
  quantify over thresholds in the band `T <= Delta(-A_thr)`, the out-of-band case is in `lowerPhase_of_inputs`. Proved:
  `lower_pass_upper`, `lowerUstar_phase`, `lowerPhase_of_inputs` (with `LowerPrelim` and `c0 < 0`), `lowerPhase_virasoro`,
  **`spinless_lower_of_inputs`** (`-C c^{-1} log c`). `langer` is discharged (`lowerLangerPhase_holds`,
  `FiveTerm/LowerLangerBridge`). Each field is implied by the current TeX lemma (C6 (1), C7 (4), C7b, C8), so the fields are true
  for the real chart but weaker than the paper; satisfiability is not checked otherwise.
- *Open:* the restatement (Best next step 1: one pass, log-free fields `combined`, `pass2` (unconditional C7b), `boas`); the four
  fields (Best next steps 2, 3, 5); `cts:lower-main`'s second display (in `c`); `cts:cauchy-dual` (2) and the signed estimate
  `cts:Kedge-signed` (inside `combined`). `teb:quant_c1_near` is not needed at Virasoro (`c0Star < 0` gives `phi_c(a1) > a1`, so
  the violator form suffices); FIVE-W needs it for `c_0^*(w,Q) >= 0` (a copy-adapt of `QuantC1Airy` in a new file, about 1.3k;
  `QuantC1Airy` is imported by Paper I and is not edited). `rem:thmOloc` is not needed here.
- *Shared lemmas (one Lean copy, agreed with Paper I's plan; Paper I prints them):* FS.1 `fs:half-cubic` (signed CFU pairing, for
  `combined`; in Lean as `fs_principal`, `fs_aux`, `fs_pairing_principal`, `fs_pairing_aux` in `SignUncertainty/FineOrderSigned*.lean`), FS.2 `fs:circle` (two-moment good circle, for `pass2`; its proof is already inside Paper I's `ct_dyadic_radius`),
  FJ `fj:lemma` (fold reduction (1) and inverse-chart transport (2), for `chart` and the C9/C15 coefficient read-off). Stated
  phase-free, they also give Paper I's log-free `thm:ct-lower`.

**FIVE-U** (headline 3; L, 25-35k, about 6k done). Closes `cts:smooth-env`, `cts:tip-shared` (done), `cts:upper-design`,
`cts:regionII-floor`, `cts:shifted-langer`, `pm:tip-match` (done), `cts:upper-vac`, `cts:transfer`, `thm:spinless-expansion`.
- *In Lean* (`FiveTerm/Upper*`, design `FiveTerm/FIVEU_DESIGN.md`), stated over any `src : ShiftSource` and
  `OuterDatum W K g1 G`, constants entering only through `(c0, gamma0)`: `smooth_env_one_virasoro` (`cts:smooth-env` (1), every
  `delta` in `(0,1)`); the algebraic half of (3) (`fStar_edge_eq`, `fDelta_edge_ratio`, `detuneD_bounds`, `detuneR_pow4_bounds`);
  **`tip_match`** (`pm:tip-match`, non-sharp `C = 500 (2/(9 pi^2)) |a1|/kTip`; about `0.246` would do numerically);
  `cts:tip-shared` complete (`pair_drift`, `pair_drift_gamma`, `tipShared_d`, `airyLinearMoment`, `airyPrimitiveDecay`,
  `airyBC_id`, `airyBC_rhs_bound_paper`, `airyBC_bnd_W0/W1/W2`; the only weight hypothesis is `W_n <= W_b <= c0`);
  `dimension_le_of_phase_le`, `sharp_upper_of_family`, `spinless_upper_of_family` (modulo `SharpUpperFamily`).
- *Skeleton:* `UpperMainInputs src W K G g1 gamma0` over the abstract comb `h0 c d b = E_delta B_D`; the test is defined
  (`upperTest src h0 c d = pairOdd u (hankelTransform src.w u)`, `u t = Re h0(sqrt(3t/c'))`). Fields one to one with the open
  lemmas: `c11_membership` (C11 (3)), `c11_first_site` (C11 (1) and C10 (3) `Psi_delta`), `c12_regionII` (C12 (2)),
  `c13_regionI` (C13 (3)), `c14_vacuum` (C14, `cts:Vc-exp`); `K_delta`, `C_V`, `C_1'`, `C_tau` are independent of `D`, only the
  threshold depends on `D`. Proved: `sharpUpperFamily_of_inputs`, `sharp_upper_of_inputs`, **`spinless_upper_of_inputs`**.
  Satisfiability of `UpperMainInputs` is not checked.
- *Open:* C11-C14 (section 1.1, headline 3, steps 5, 7, 9, 10); statements unchanged at `80acaed64`.

**FIVE-W** (headline 3; L, 5-8k). Closes `ctu:main`, `ctu:O1` (`c_0^*(w,Q)` clauses), `ctu:table`, `ctu:weight`, `ctu:strip`,
`ctu:tip-window`, `ctu:tip-kernel`, `thm:fixed-weight-expansion`. Needs FIVE-L, FIVE-U, PM-0b (`ctu:jets` at `(w,A)` for the
`(w,Q)` constants), `fixedWeightAxioms_of_problem`. Route notes (PR 307 corrections in the `ctu` transfer table): the C10
descendant factor is `log(1 - e^{-4 pi mu_l F(v)})` (unnormalised), and the Region-I `Q`-ratio at `s^2 = -a(x)` is
`Q(e^{-4 pi xi_*})/Q(e^{-4 pi x})`, the reciprocal of the normalised `Q` factor of the slit modulus, not `1`. Design rule: keep FIVE-L/FIVE-U stated over general data so FIVE-W is an
instance (5-8k) rather than a copy (15-25k).

**PM-0b** (headlines 3, 4; M, 2-3k). Closes `ctu:jets`, `ctu:piece4`, `cts:base-jets`, the rest of `ctu:common-functional`
and of `pmix:jets` (`j(w,A) = alpha_tip g1(w,A)`, `ctu:g13A`, the defect identity and the equality criterion). Route: the TeX
proves `ctu:jets` in the half-plane coordinate `P = (zeta - 1/zeta)/(2i)` (`Re P > 0` on `Omega`, `P o sigma = P`), every odd jet
a real integral `J_k` of the even data `f(t) = log(A(x(t))/A(xi_*))` (`ctu:all-outer-jets`), the geometry-only jets being
`cts:base-jets`. So: a half-plane Schwarz integral of `f` (`Complex/HardyHalfPlane`, Paper I's half-plane outer files)
multiplied onto `Gout`, giving `OuterDatum W_A K g1 (Gout * G_{A,4})`, not a strip construction of `G_{A,4}`; then
`comb_minimum` gives `j = alpha_tip g1`, linked to `pmix_jensen` by `I_1 = int F/t^2`. Shift-term algebra checked:
`-4 pi r_i xi_*/sqrt2 . 8 alpha_tip/pi = -12 xi_bar r_i` (`alpha_tip = xi_*/(4 sqrt2)`, `xi_bar = xi_*^2/3`). Suits bounded runs.

**PA2** (headlines 2, 4; L). Open: `dsl:one-level-clusters`, `dsl:near-opt-mass` beyond `(H_w)` (done there: `one_level_clusters`,
`one_level_near_opt_mass`), `sr:single-level`, `dsl:hb-clusters`, `dsl:hb-mass`. The cluster structure needs only the `O(1)` law; the
exact first atom `d_1` and `(t_2^* - t_1^*) c^{-1/3}` need `c_0^*` (FIVE-W; it uses `rig:R`, not `bl:norm`). The HB forms (`dsl:hb-clusters`: inactive extra sites by `ds:primal` (d);
`dsl:hb-mass`: raw masses on the fixed window and on shrinking windows `h_n = o(1)` by Markov on the moment bounds) need PM-3.
Needs W-P5, FIVE-W, PM-3 (HB forms).

**SLK, rest** (headlines 2, 4; S). HB1 for the identification of the node data at general `(P,Q)` (`hb_blnorm`, `hb_blnorm_s`
  take the node data for a given `D`). Optional in-place edits: re-derive `proposition_P_general`, `lemmaQ_general_part3` as the
`eta = 0` case of `densityHyp_of_slack`; make `continuousOn_deriv_virasoroDeltaChart`, `chartUT_mem_Icc_of_between`,
`cardyNorm_pos_of_nonzero_P` and the ArcBounds `deriv_airyAiC_ofReal` public (primed copies are in `SlackFeasible`).

**W-T2w, general `m`** (headline 4, HB level; L, 6-8k). `(f,r) = (m, m-1)`: `ut:ideal` (a), (b) at `m >= 3`, Remark T2.1,
`ut:Vac` for general `f >= 2`, `ut:IIF`, `ut:I`, `ut:III` for general finite real factors. No mathematical blocker. Not needed for
headlines 2, 3; needed for the HB taper `(m_0, m_0-1)` of `pmix:rigidity`(c) at `m_0 >= 3` (PM-3), since the design side at
`(w, Q = 1)` is open beyond `(2,1)` while the PM-2 transfer is design-independent. Steps: (1) `MZeroDesign m n` (real zeros
`p_1 > ... > p_m` with pair sites); (2) K7W, phase and inner comb for `r` Blaschke factors by induction (`mul_blaschkeT`,
`PhaseComb.mul_blaschkeT`); (3) Regions I/II for `f = m`, `gamma = m + 1/2`; (4) lobe (power `(x - xi_*)^{-(2f - 1/2 - r)}`),
band, far band and vacuum core with `F_{m,m-1} = FK^{(m)} (pi lambda/(2 sqrt 2))^{m-1}`; (5) port `IdealApprox*` (about 1.7k) to
`m` zeros ((b) then follows from Fatou and (a)).

**PM-1, rest** (headline 4; S). `pmix:liminf` identification with `c_0^*(w,Q_i)` (section 1.1; needs FIVE-W); optional: `pmix:ramped`
uniform in `d in [0, d_0]` (rerun `rampedBumped_positive` with `d` variable; no downstream Lean consumer needs it), the separate
`|G| <= C (1+|u|)^{-5/2} e(u)` bound of `pmix:punif` (unused downstream).

**PM-2, rest** (headline 4; M). General `(f,r)` (design side first, then a copy of `VacTwoZeroWindow/Core/VacTwoZero`, about 700
lines); the two-sided second limit (at `(2,1)` within reach: `int_{|u|>R} |W_2| -> 0` and the window limit; `pmix:rigidity` uses
only `limsup_le`); the consumer ports are done (`Mixtures/SourceRigidity`, `SourceTwoLevel`).

**PM-4** (headline 4; **done** — moved to section 2.2).

**FT-H4b** (headline 4; M-L). Realign `FTH4b` to the paper's H4b (`fold_tip_universality.tex`, `ft:hyp`, `\textlabel` `ft:H4b`):
general Hermite-Biehler data `(P,Q)`, terminal index `m`, support clause (a), one-sided designs (D1)-(D4); then Lemma WP
(`sr:window-pairing`), Lemma WR (`sr:WR`) and C5(c) at every HB level (`FTSigma` is the Airy level only). The present `windows`
field assumes tail bounds that are conclusions of WP, so it is replaced, not extended; re-point Concordance row C5c. Needs FT-1,
`Upper/Rigidity`.

**PM-3** (headline 4; L). `pmix:hbphase`, `pmix:hbtap`, `pmix:rigidity` (rest per section 1.1); `gt:2.1`, `gt:2.4`-`gt:2.6` for mixtures. Needs PM-1,
PM-2 (`pmix:vac`; consumer ports done), PM-4, PA2 (one-level part: `dsl:one-level-clusters`, `dsl:near-opt-mass`;
`pmix:rigidity`(c) cites `dsl:hb-clusters`, `dsl:hb-mass` only as forward pointers), W-T2w (`ut:ideal`; general `m` for the HB
taper), SLK, FT-H4b, W-P6.

**INT-2HB** (headline 4; L). `int:hb-reserve` (any strict HB pair; `m_0 = 1` is `int:reserve`), a sharp law with matching
upper bounds since PR 307 (`int:hb-res-sharp`: normalised infimum `(kappa_N^res + o(1)) n^{-1/3} eta`, maximal reserve
`R(B_n - eta; F_n) = (kappa_N^res/p_N + o(1)) n^{-1/3} eta`, uniformly for `0 < eta <= H(n)`, fixed source and HB pair). Needs
PM-3 (`pmix:rigidity`, `pmix:hbtap`), PM-2 (`pmix:vac`), W-T2w (`ut:ideal`), SLK, DU-F, PA1 (`ds:primal`), PA2
(`dsl:hb-clusters`), `pmix:o1`, `pmix:rebase`, `pmix:dominated` (PM-5 for the dominated clause).

**HB1** (headline 4; S-M after its inputs). `gt:hb` for general `(P,Q)` (the single-component case of `pmix:rigidity` with
`int:hb-reserve`, `sr:single-level`); closes `wone:ftlfw`, `wone:genlower` for all `m_0`. Needs PM-3, INT-2HB, PA2, FT-H4b, SLK,
PA1, LP1, Paper I M8 (TE.0' for all `(P,Q)`, via the `ChartCompactness` instances).

**PM-5** (headline 4; S). `pmix:main` (assembly), `pmix:dominated` (Corollary PM-S, general `lambda`), `pmix:floor-criterion`
(PM-S0: uniform Cardy floor iff `lambda({0}) > 0` and `A(x) > 0`; cf. Lean `FloorData`). Needs PM-0 to PM-4, PA2 (`pmix:main`
(3)-(5)), INT-2HB, INT-3, INT-4, FIVE-W (`ctu:c0`), PM-0b.

**SPIN-Z** (headline 1; M analytic part, certificates later). `isl:main`, `isl:finite`, `spinnotes:K1`, `K2`, `K4`, `K4a`,
`L0a`-`L9`, `L3a`, `L8a` (`spinnotes:K3` left the paper at PR 311; it and the explicit real-collar bounds are in the note
`notes/tex/spinning_integer_alternative_proofs.tex`). Computer-assisted in the paper: exact-rational whole-slit bounds and the first
intermediate-spin regime (K.4(2)); Arb enclosures for the small-spin edge excess (K.4(1)) and the remaining intermediate boxes
(K.4(3)); exact-rational plain bounds (K.4a). `spinnotes:L8a` (sharp-cutoff rigidity: the tapered sum tends to the normalised Airy
profile `G_Ai/(2 A_*)`, `G_Ai = -Ai^2/(u - a_1)`, with total-variation limits of the signed and absolute energy measures) and
`spinnotes:L3a` (variable-radius unslit tip averaging, the scaled tip bound `C a^P d^{-P} e^{-c a d^{3/2}}`) are planned here; L.8a
rests on L.5-L.7, `ap:lemHp`, `ap:thmQ`(4), `lam:thmB` (equality case, `airy_sign_equality_iff`).
- *Decision:* in Lean the enclosures are one named hypothesis structure `SpinZEnclosures`, one field per item, each stated
  exactly as the paper's check asserts it, with its box; SPIN-Z proves `isl:main`, `isl:finite` (and L.8a) from it. Kernel-checked
  certificates wait until the other headline work is done (`decide +kernel` on exact rationals, or Mathlib's `dyadic_interval`;
  the `QVCheck` `native_decide` chain is not an acceptable precedent).
- *Fields (paper at `80acaed64`):* (1) the small-`Delta` compact symbol `P_4` on `0 <= Delta <= 5e-5`: the edge saddle excess, a
  bound on the nonnegative clamped excess `(E_eff - Delta Re h_4 + Delta r_*)_+` with `D_e < 3.73` (Arb), and the whole-slit
  trial-radius envelope `T_{A,Delta}` with `D_s < 10.94` (exact rational), so `D_tot < 14.67` (the statement also allows
  `<= 16.46 < 20`) and `12 C_1^new <= -c_{1,P_4} Delta^2`, `c_{1,P_4} > 40`; the positivity `Re e_a > 0` on slit and edge
  (`c_e/x_0^2`, `c_e'/u_0^2`); (2) K.4(2), `5e-5 <= Delta <= 0.0038`: one unregularised symbol `P_{4,0}` (explicit coefficient
  matrix of `p_2, p_3, p_4`) with the exact-rational bounds `(2/pi) int S/v^2 < 13.2 Delta^2`, `(2/pi) int (E + Delta r_*) < 8.4
  Delta^2 + 0.00165 Delta`, weighted Wiener integral `< 70`, giving `12 C_1^eff <= -4.2 Delta^2 <= -1.05e-8`
  (`verify_spinning_integer_pf_unregularized.py`, now the only K.4(2) route); (3) K.4(3), `0.0038 <= Delta <= 0.072`: a finite
  contiguous box cover (twenty boxes in the Arb log, seven in the reduced-envelope route) with the stated `W_abs` bounds; (4) K.4a:
  `f'' < -117.6` on `[0, 0.004]` (so `c_quad = 58.8`) and `12 C_1^orig < 0` for `Delta in [0.072, kappa/2)`. The former real-collar
  item (`W = 0.037`, the `e_a` step, `h_4/xi^2 < -0.55`, `M_15`, `M_{e^{0.5}}`) is no longer a paper input: K.1 now holds for every
  `b_t > 0`, a collar existing by continuity at the tip and `|w(0)| < 1`. K.2 covers only the unregularised multiplier
  `M_{K,0} = exp(a Delta P_{K,0})`, tip vanishing of order 2, inversion at `|q| = 3/2` costing `O(Delta |zeta|^2)`; L.3a and L.4(b)
  use `M = exp(a Q)` and `h = P_{4,0}(q_*)`; L.2(2)'s spin-zero floor is `rho_B(2s,0) * 2s >= (c_2/4) s e^{2 gamma a}`; the H.1
  folded slit density is at most `2 v'(x)/(pi X)`; L.5 is stated for a bounded range of cutoffs `u_{1,n}` (`T_n = kappa_* a - s_a
  u_{1,n}`), as L.8a needs. Fields (1) (slit part) and (4) need only exact-rational or elementary-function bounds; the edge
  enclosures need a Ball layer (Mathlib has none: reuse `ThirdParty/interval`). A smaller `c_quad` may be possible (unverified,
  `R557`).
- *Lean-friendly discharge routes* (`notes/K4_LEAN_PATH.md`, exact-rational or interval certificates plus an analytic transfer
  proved there; `python-flint` not needed): an exact-rational `P_4` edge (`verify_spinning_integer_p4_edge_{outer,tail,full}.py`;
  `D_e < 4.759`, `D_tot < 15.70`, `c1_{P4} > 43.10`; the weaker constants still close Part L); a seven-box cover for (3)
  (`CERT_POLY_LEGACY=0`, worst margin `-1.776e-4`), built on the global plain tip bound `f'' < -111` on `[0, 0.072]`
  (`verify_spinning_integer_plain_global.py`); the explicit real collar of the alternative-proofs note is a further, now optional,
  route. The single-anchor homotopies are notes-level, not consumed by Part L. A field discharged by one of these routes is stated
  with that route's constants and says so; the paper's form stays the default.
- Needs SPIN-S4 (done), SPIN-D (done).

**INT-T, rest** (headline 1; L, about 3.6k done of 8-12k). `int:cheb` at the paper's floor `640 N^2` (filtered inverse on the
oversampled grid: `Corr (2(M+1)) M R` for `R >= 320` by a de la Vallée-Poussin taper, `L^1` norms of the `K_j`, a contraction on
the `l^infty` cube; no obstruction known, 1.5-2.5k; check whether `int:main`'s prefactor depends on the floor exponent: if not,
`int:cheb` is off the headline path since `int:atom` takes an abstract floor); `int:sonine` and `int:repair` for real `w >= 1` (Lean has
integer `w` only, `Integrality/{WeberLaplace,HankelSonine,RepairHankel}`, with `max 4 (2048 pi^2 B^2 e^{16 pi B})` for the
`int:sonine` bound in place of the paper's constants; the real-weight route compresses the Hankel operator at real `w >= 1/2`,
since PRs 299/301). INT-R uses the abstract projection repair (real `w >= 1`); INT-R0
needs pointwise crossing identities on the band.

**INT-2** (headlines 1, 4; M-L). `int:reserve` (sharp joint large-charge law: normalised slope `(kappa_res + o(1))
c^{-1/3} eta`, maximal reserve `(2 kappa_res + o(1)) c^{-1/3} eta`, `kappa_res = 1/(2 ell_V L_*)`, uniformly for `0 < eta <= 1`;
variational formula `int:reserve-var`, i.e. `ds:E`(c)), `int:strict-weak`. Lower half: inputs in Lean for `(H_w)` and positive
mixtures, modulo the `bl:norm` check; upper half needs PA2 (section 1.1, headline 1, step 2).

**INT-3** (headline 1; M). `int:main` and `int:hb-integer` (the HB-site version, with the same cluster-mass and concentration
clauses at every fixed terminal or later HB node). Needs INT-1, INT-2, INT-T, W-P6; PA2 (`dsl:one-level-clusters`, `dsl:hb-mass`,
`dsl:near-opt-mass`) for the cluster clauses; FIVE-W (`ctu:main`) for the five-term corollary; INT-2HB for `int:hb-integer`.

**INT-4** (headline 1; M). `int:obstr`(a): **done at `(H_w)`** (`Integrality/IntegerObstruction.lean`: `int_obstr_a`, `int_obstr_a_primal`; supremal integer gap attained, `Delta^Z = Delta^R` iff some attaining real measure is integer-weighted, and at every fixed charge `12 S <= c~` strictness iff every attaining real measure has a non-integer atom); mixtures/common sources: rerun over `SourceDualSetupCore` now that PM-4 is done; (b), swap-invariant spin cones, is INT-S.

**INT-S** (headline 1; L). `int:axis-trace` (since PR 299 a weighted Hölder bound `||Phi||_1 <= 50 a^{-1/7} M_2[Phi]`, S2.4, no
axis-trace decomposition), `int:cheb2d`, `int:cheb2d-explicit`, `int:cos2d-repair`, `int:cont-spin` (any repair budget
`sum b_k <= 1/8`; lattice `b_k = 1/(8k(k+1))`; INT-7C drops `2 pi e R <= m`; continuous-spin moment orders `O((a+R^2)/log a)`;
uses `dsl:reserve` with weights `(1/2,1/2)` and the Virasoro product source, which is exactly the Lean `dslReserve`), and
`int:obstr`(b). Needs SPIN-S4 (done: `spinS4`, `s4:eSlack`), SPIN-D (done), DU-G (done), INT-1 (done: `int:counting`), INT-4, INT-T, FIVE-U
(`cts:transfer`).

### 2.2 Done packages (one line each; declarations in `THEOREM_MAP.md`)

- **FIVE-0** (Virasoro data): constants, Langer, phase locking, half-disc geometry, outer function `Gout` with `gout_outerDatum`,
  chain to `cts:main`, jets `g1Out_eq_g1Vir`, `g3Out_eq_g3Vir`, `gamma0_eq_gamma0Of_out`, `comb_minimum_virasoro_c0Star`
  (`FiveTerm/`, about 16.7k). Open part is PM-0b.
- **FIVE-S** (Virasoro outer function): `outerS1`-`outerS4` (`FiveTerm/Outer*`, `Complex/StripBdryFunctional`; about 12k).
- **W-P5**: design side at every weight (`Upper/Positivity/VacuumBumped`, `Upper/Assembly/BumpedDesignWindow`,
  `FoldTip/InstancesAllWeights`).
- **W-P6**: `theoremC15UpperInput_probW`, `ft_fixedWeight_all`, `corollary_two_four_all` (`Upper/Ramped/RampedBump*`). Optional:
  re-derive `rampedWindow_part` from `rampedWindow_part_gen` and `theoremC15UpperInput_prob` from the `probW` form.
- **W-T2w at `(2,1)`, SE3 (zero and offset forms)**: `twoSimpleZeroTransfer_all`, `theorem_two_five_all`, `theorem_two_six_all`,
  `wone_clark_two_level_boundary_all`, `se_crossing_corollary` (`TwoLevel/TwoZeroBump*`, `TwoZeroTransferW`, `WOneFiveClarkAll`,
  `SoftEdgeCrossingCorollary`; the offset form `se_crossing_corollary_offset`, `se_crossing_corollary_offset_bounded` in
  `TwoLevel/SoftEdgeOffsetCorollary`). Optional cleanups: drop the unused `prob.w = 1` from `twoZeroF_eq_windowMeasureNormK`,
  `twoZero_band_bound`, `twoZero_window_comb` (and delete the `_w` variants); re-derive `twoZero_regionOne_a/b` from the `_lower`
  versions; generalise `twoZero_lobe_small/near/bound`, `twoZero_far_bound`; make the `_w1` forms thin wrappers of the `_all`
  versions.
- **DU-G**: `ds:E` (a), (b) compact `F`, (c), `ds:farkas` (`Duality/`). Route: finite-dimensional separation plus Carathéodory and
  a vague limit along an ultrafilter (`RealRMK.rieszMeasure`), no `[0,1]` compactification. Optional re-derivations:
  `TwoLevel.constrained_strong_duality` as clause 3 of `theorem_E_a`; `FixedWeight.theorem_E*` and Virasoro
  `Duality.theorem_E_b/_c` from `theorem_E_b_compact(_empty)`; `Upper.Rigidity.exists_vagueLimit` as the `Y = R` case of
  `exists_vagueLimitAlong`; `Duality/Farkas`, `Duality/MeasureCompactness` are subsumed. Optional corollary:
  `T_F^{[infty]} = T_V(c~;F)` for compact `F` (from `theorem_E_b_compact`, `ds_LP_i`, `ds_LP_b_imp_a`).
- **PA1** (every fixed charge `0 < c~`, `12 S <= c~`): `compact_negative_mass`, `dsl_strip_fixed_a` (`_of_floorAt` for sources), `T_V_pos`, `theorem_primal`
  (`Duality/Primal/`); `dsl:strip-fixed`(b) is positivity only.
- **PA2, one-level part** (`(H_w)`): `near_opt_isVagueLimit`, `one_level_clusters`, `one_level_near_opt_first_moment`, `one_level_near_opt_mass`
  (`Duality/Primal/{OneLevelClusters,OneLevelMass}`).
- **LP1, LP1b**: `ds_cay_*`, `ds_cont`, `ds_mom` (with `lagP_oddFam_sharp`: `C_w = (2+w)/(2 pi)`), `poly_compact`,
  `positive_ray`, `ds_LP_i/ii/iii` (`LP/`, `Measure/PolyGrowthExtension`; design `LP/LP1_DESIGN.md`).
- **SPIN-F** (`Spin/`): `spinS1a`, `spinS1b`, `spinS1c`, `spinS1d`, `spinS1e`, `spinS21`, `spinS22`, `spinS22b`, `spinS23`,
  `spinS24`, `spinS3`, `scalC1`, `scalC3`. Modelling choices of the S1-S2.4 skeleton: holomorphy in two variables is stated separately in each variable (no Hartogs in Mathlib); the derivative-bound clause of S2.4 (1) and the `T`-invariance remark of S1 (a) are omitted.
- **SPIN-S4** (`Spin/SpinS4*.lean`, 30 modules): all fourteen `s4:*` results are proved unconditionally. The twelve intermediate
  propositions `spinS4_2_1`-`spinS4_6_1` (`SpinS4_2_1`-`SpinS4_6_1` of `SpinS4Statements.lean`) assemble in
  `Spin/SpinS4Assembly.lean` into `spinS4_4_4` (`s4:4.4`) and `spinS4` (`s4:S4`); `spinS4_4_4_of_props`, `spinS4_of_props` are the
  modular forms. The Lean statements of `s4:2.3`, `s4:5.2` and the truncated inverse match `spinning_s4.tex` (`spinTruncInv` sums
  the outward `spinDeltaA`; `SpinS4_2_3` has `∀ C_x` outside the constants and the hypothesis `0 <= x_1`; `SpinS4_5_2` has chart
  endpoints `virasoroUChart n ((xi_* -+ r_0)^2/3)`).
- **SPIN-D** (`sd:R` partial since PR 307): `spinDM`, `spinDP`, `spinDSD`, `spinDW`, `spinDV`, `spinDA`, `spinDLP`, `spinDR`
  (the marginal Airy law; the `dsl:hb-mass` concentration clause of `sd:R` waits for PA2, then extend `SpinDR` in place), and
  `dslReserve` (`dsl:reserve`,
  `d = 2` swap-invariant form) (`Spin/SpinD*`). The exponential `L^1` bound `spinTestClass_exp_L1_le_M2` replaces the paper's use
  of `spinnotes:S24` in `sd:V`, `sd:A`. Lean's `a >= 2` is the paper's `c >= 25`.
- **SLK** (`u`- and `s`-variable), **STAB** (`rem:thmBstab`; `se:3.1`; `se:terminal-stability` all clauses: `hbMultiI_expansion`, `hbCommonShift_lt_one`, `se_terminal_stability_boundary`; `Stability/{MultilevelBase,MultilevelExpansion,HbBoundaryCoord}`), **SR-COR**
  (masses, positions and barycentre): `Blowup/NormLimit*`, `Stability/`, `Upper/Rigidity/{SpectrumCorollary,ClusterBarycentre}`.
- **INT-T** (to its scope): `int_closed`, `cheb_explicit`, `ShellSetup.shell_inv`, `repair_identity_*`, `hankelDual_bound`, and at
  integer weights `weber_laplace`, `fourier_concentration_radial`, `hankelSonine_inv`, `hankel_repair` (constant `sonineRepairConst`)
  (`Integrality/`).
- **INT-1** (`int:atom`, `Integrality/{AtomBounds,AtomCell,Atom}.lean`): `int_atom_common`, `int_atom_cheb_explicit`,
  `int_atom_fixedWeight`, `commonSource_cardyDensity_lower`, `commonSource_counting_bound`, `atom_cell_step`; unconditional.
- **PM-0, PM-1, PM-2** (to their scopes, all labels partial; PM-1 includes the common-source `pmix:o1` lower half, `Mixtures/Source*.lean`): `Mixtures/` (designs `PM0_DESIGN.md`, `PM1_DESIGN.md`,
  `PM2_DESIGN.md`).
- **DU-F** (`se:cdual`, unconditional at every fixed charge): `TwoLevel/ConstrainedDualitySE.lean` (`se_cdual_fixedWeight`, `_fixedWeight_singleton`, `_floor`, `_common`, `_mixture`).
- **SPIN-M** (`sd:spinmoment`, unconditional): `Spin/SpinMoment*.lean`.
- **PM-4** (`pmix:duality`, every fixed charge in range): `Mixtures/{DualMajorant,ThermalSeparation,Primal,DualityLP,Duality}.lean` (`pmix_duality_common`, `pmix_duality_mixture`).
- **PM-2 consumer ports, `pmix:o1` comparison, `pmix:liminf` (conditional)**: `Mixtures/{SourceRigidity,SourceTwoLevel,O1Liminf}.lean` (`src_sigma_unconditional`, `src_two_level_exclusion`, `src_theorem_two_six`, `pmix_o1_component_comparison_unconditional`, `pmix_liminf_of_component_c0`); scopes in section 7.7.
- **FT-CC**: `FoldTip/ChartCompactness.lean` (`ChartCompactness`, `uT_bddAbove`, `subseq_extremal`, `chartCompactness_limsup_ereal`, `chartCompactness_limsup`, `chartCompactness_profile`); instances `FoldTip/HankelChartCompactness.lean` (`radialRigidity_to_chartCompactness` from Paper I's `RadialRigidityPackage`, `hankelPrescribed_chartCompactness`, `hankelPrescribed_liminf_lower` (`gt:7.5`), `hankelPrescribed_profile_rigidity`, `shellReduction_littleO`; no edit of `SignUncertainty/`) and `FoldTip/FixedWeightChartCompactness.lean` (`fixedWeight_chartCompactness` for any `FixedWeightProblem` and `HermiteBiehlerData`, `_limsup`, `_profile`, `_virasoro`, `_clark`).
- Earlier lanes: **A** (`O(1)` upper bound at `w = 1`, `Upper/Ramped/`), **B** (`Sigma_0`, `Sigma`), **C** (`N = 1`), **D**
  (bump at `w > 1`, P1-P4), **TL1-TL6** (two-level lane), **FT-0, FT-1, FT-2** (`FoldTip/`). Lessons kept: state the general lemma
  in its own file and re-derive the old declaration under its old name; state weight-one lemmas in an abstract-integrand form
  first (`rampedWindow_part_gen`). Open follow-ups of TL: the `integrable` field of `TwoZeroTransferData`; a shared core builder
  for `bootstrapHB_of_YVForWThr`/`_Clark` (about 200 duplicated lines).

### 2.3 Dependency edges and waves

Edges (a package waits for everything it needs; checked against the `\ref`s of each proof in the TeX at `80acaed64`):

```
FIVE-0 (done) -> FIVE-S (done) -> {FIVE-L, FIVE-U} -> FIVE-W <- W-P5, W-P6 (done), PM-0b        [headline 3]
shared FS.1, FS.2, FJ (with Paper I) -> FIVE-L fields combined, pass2, chart                       [headline 3]
DU-G (done) -> PA1 (done) -> {INT-4 (H_w done), DU-F (done), PM-4 (done)} ; PA1 + W-P5 -> PA2 one-level (H_w done) ; + FIVE-W -> PA2 rest  [headline 2]
SPIN-F (done) -> SPIN-S4 (done) -> {SPIN-Z, INT-S}                                        [headline 1]
SPIN-D (done) + Sigma (done) + W-P5 (done) -> SPIN-M (done)                                         [headline 1]
INT-T, INT-1 (done) ; SLK + W-P6 + DU-G -> INT-2 lower ; + PA2 -> INT-2 upper ; INT-1 + INT-2 + PA2 (+ FIVE-W) -> INT-3  [headline 1]
PA2 (dsl:hb-mass) -> sd:R concentration clause                                                       [headline 1]
INT-1 + INT-4 + SPIN-S4 + FIVE-U -> INT-S                                                            [headline 1]
PM-1 + PM-2 + PM-4 + PA2 + W-T2w + SLK + FT-H4b -> PM-3                                              [headline 4]
PM-3 + SLK + DU-F + PA2 -> INT-2HB -> {HB1 (+ Paper I M8), PM-5 (+ INT-3, INT-4, FIVE-W)}  [headline 4]
```

| wave | open packages | why |
|---|---|---|
| 1 | FIVE-L restatement, FT-H4b, SLK rest, INT-T rest, PM-0b, W-T2w general `m`, PM-1 rest, shared FS.2/FJ (2) | no open parent |
| 2 | FIVE-L fields, FIVE-U, INT-2, INT-4 for sources, PM-2 rest | need wave 1 at most |
| 3 | FIVE-W | |
| 4 | PA2, INT-3 (main part earlier), INT-S, SPIN-Z | SPIN-Z with `SpinZEnclosures` |
| 5 | PM-3 | |
| 6 | INT-2HB | needs PM-3 |
| 7 | HB1, PM-5 | |

A wave is an order, not a schedule. INT-2 is in wave 2 because its inputs are done; INT-3's main statement needs only INT-1 and
INT-2, its corollaries wait for FIVE-W and PA2.

### 2.4 Staffing and practice (owner decisions)

- 2026-11-28 (owner): SPIN-Z may keep the computer-assisted enclosures as the named input `SpinZEnclosures` for now; kernel-checked
  certificates are not on the completion path. `int:repair` / `int:sonine` at integer weights `w >= 1` are acceptable, since the
  main results use only integer weights; move to real `w` only if the change is easy (do not open a real-weight route for it).
- No time boxes; a stalled route is a ledger row, not a stop. At most three runs at once; launch only with at least 1.5 GB disk free.
- Since 2026-11-26 (owner): no new Sonnet agents; agy `gemini-4-neon-medium` for the hardest L steps, agy
  `gemini-4-hydrogen-medium` for bounded steps, Haiku for docs and `THEOREM_MAP.md` rows. Agy drafts are checked against the
  paper before landing (as for every `from an agy draft, checked` commit).
- For each long lane (FIVE-*, SPIN-*, PM-*) five pushes adding results without moving the lane's headline force a direction
  statement.
- Shared files: the umbrella `FormalResearch/ModularBootstrap.lean`, `THEOREM_MAP.md` and this plan take targeted edits after
  merging `origin/master`; never apply an agent's stale umbrella or plan as a diff.

### 2.5 Code to reuse

- In reasoner: `Complex/Montel` (`montel`, `montel_family`), `Analysis/Scheffe`, `Analysis/QualCompact` (`qual_compact`,
  `qual_compact_real`: Paper I's `lem:qual-compact`); `Duality/VagueCompactness` (`IsVagueLimitAlong`); `StripBand/StripPoissonRep`,
  `Complex/StripPoisson`, `Complex/HardyHalfPlane`, `Complex/HalfDiscCauchy`, `Complex/HalfDiscPoisson`, `Complex/SchwarzReflection`,
  `Analysis/VanDerCorput`, `Asymptotics/DyadicAbsorption`; Paper I's `SignUncertainty/Ct*`, `Fct*` stacks (section 6).
- External: `PrimeNumberTheoremAnd` (rectangle contour shifts `ResidueCalcOnRectangles.lean`, `norm_fourier_le_integral_deriv_div`;
  port selectively); `rmt-foundations-lean` (Herglotz/Stieltjes; Lean v4.35.0, needs porting to reasoner's v4.36.0; see the Lean
  skill's `references/mathlib-bump.md`); `HardySpace_formalization` (no licence file: reference only). Nothing found for
  two-variable `(h, hbar)` modular kernels, `int:cheb`, `int:sonine`. Mathlib after the pin: Poisson-Jensen (#42475), `besselJ`
  derivative recurrences (#42825, #43853), `dyadic_interval` (#45427 and follow-ups; an alternative for SPIN-Z certificates).
  Reasoner is on Mathlib v4.36.0 (`fc4f59e`); check which landed before that tag.

## 3. Not planned, and tier 2

| item | labels | reason |
|---|---|---|
| **INT-L**, lattice integrality | `int:lat-reserve`, `int:poinc`, `int:amgm-floor`, `int:lat-repair`, `int:int-spin` | conditional on (CLM) (Chang-Liu-Ma, external) and on the SPIN-Z enclosures |
| `N = 1` reduction | `n1:P1` | physics bookkeeping (characters, `eta^3/theta_3`); Lean takes the reduced problem as the definition |
| numerical decimals | `0.4837...`, `0.2070524`, `1.2180230048`, `21.0680128515`, `c_0^* = -0.0713301`, `d_2^* = -0.3462493`, tables of `ctu:table` | numerical evidence; the closed forms are planned |
| explicit Bessel constants | `vlo:BesselConst` (`kappa_0 = 1/4`, `kappa_1 = 1`) | Lean's constants are existential; not needed downstream |
| vacuum-slack Theorem J | `int:Jslack` (alias of `vlo:J`) | used only by INT-L |
| unflavoured `N = (2,2)`, real weights outside `(H_w)` | main-text remark; `wone:ftlfw` for real `w` | `V = f_a * f_a` is not of Cardy type; real `w` can be revisited after PM-0 |
| FT-3..6 beyond FT-CC | chart-form Lemmas 1-2, C5d `m >= 2`, Lemma FT-R log rate | Paper I's plan owns `ft:L1`, `ft:L2`, `ft:riesz`, `fto1:mellin` (with its M8); this plan has no `FT-7` |
| five-term `c_0^*` clauses outside `(H_w)` | `ctu:scope` remark | out of the paper's scope |
| Theorem FQ (notes) | `fq:main` (`CFT/notes/five_term_quantisation.tex`) | a coefficient dictionary (jets -> five constants, both papers), not a Paper II result; the Virasoro constants are already Lean theorems (FIVE-0) and FJ (2) gives the read-off; its open abstract quantisation theorem (R558) is not a target |
| `O(c'^{-1})` upper remainder | `CFT/notes/five_term_remainders.md` (R561) | unverified candidate, used by neither paper |
| multiscale dyadic bootstrap and half-moment (tier 2) | `ctl:dyadic` below the top scale, `ctl:half`, `cts:half` (labels stay planned) | since PR 313 not used by the lower bound (C7b needs only the top scale `R_J`); keep for completeness only |
| **LP2 rest** (tier 2) | `dsl:reserve` for general `d` (label stays partial) | its only headline use, `int:cont-spin`, needs the `d = 2` swap-invariant Virasoro form, which is `dslReserve`; the other citations are a remark in `dual_spectrum.tex` and INT-L |

## 4. On master: headline declarations

Unconditional, pinned axioms. "Scope" is the Lean statement's scope, sometimes smaller than the paper's.

| result | TeX | Lean headline | scope |
|---|---|---|---|
| Lower bound `T_V >= T_* - C` | `wone:genlower`(1), `vlo:J` | `fixedWeightLowerBoundInput_of_problem` | every `(w,Q)`; zero vacuum slack (W4 shape) |
| `O(1)` two-sided law, exact-gap crossing measure | `ds:E1`, `ctu:O1` (first inequality) | `theoremC15UpperInput_probW`, `corollary_E1_all`; `w = 1`: `virasoro_corollary_E1_unconditional`, `n1_corollary_E1_unconditional`, `theoremC15UpperInput_prob` | every `(w,Q)` |
| Two-term law, `o(c^{1/3})` | `ds:E1` | `virasoro_corollary_E1_littleO_unconditional`, `thresholdUpperLittleO_prob` | weight one |
| Property (P), `Sigma_0`, `Sigma` | `sr:P`, `sr:Sigma0`, `sr:Sigma` | `designPropertyP_probW`, `sigmaZero_unconditional_probW`, `sigma_unconditional_probW` (and Virasoro, `w = 1` forms) | extremal measures, every `(w,Q)`; `f = 1` designs, far-first-site family omitted |
| Tip blow-up, Theorems C, R1-R3 | `bl:T`, `rig:R` | `proposition_T_of_problem`, `concrete_blowup_theorem_R3_general` | every `(w,Q)` (`Att` a hypothesis, as in the paper) |
| Crossing sum rule, duality, exact-gap measure | `fw:*`, `ds:D1`, `ds:M`, `ds:E`, `ds:farkas` | `theorem_fwC_unconditional`, `theorem_E_a`, `theorem_E_b_compact`, `theorem_E_c_reserve`, `farkas_separation`, `farkas_finite` | every `(w,Q)`; (b) under `0 < T_V`; `ds:farkas` without the symmetry clause |
| Primal attainment | `ds:primal`, `dsl:strip-fixed` | `theorem_primal`, `dsl_strip_fixed_a`, `T_V_pos` | `(H_w)`; every fixed charge `0 < c~`, `12 S <= c~`; analyticity clause replaced (5.1) |
| Theorem LP | `ds:LP`, `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact`, `dsl:positive-ray` | `ds_LP_i`, `ds_LP_ii`, `ds_LP_iii`, `ds_cay_iff`, `ds_cont`, `ds_mom`, `poly_compact`, `positive_ray` | `(H_w)` |
| Clark curve, `se:3.2` | `gt:2.1`, `wone:genlower`(2), `se:3.2` | `concrete_two_level_theorem`, `theorem_W1prime_two`, `A2star_lipschitzOn` | every `(w,Q)` |
| Corollary 2.4, Theorems 2.5, 2.6, T2, Clark boundary, `se:3.3` | `gt:2.4`-`gt:2.6`, `ut:T2`, `wone:clark`(c), `se:3.3` | `corollary_two_four_all`, `theorem_two_five_all`, `theorem_two_six_all`, `twoSimpleZeroTransfer_all`, `wone_clark_two_level_boundary_all`, `se_crossing_corollary`, `se_crossing_corollary_offset` | every weight; two-zero designs `(2,1)`; `se:3.3` zero and compact offsets |
| Normalisation limit, stability, clusters | `bl:norm`, `rem:thmBstab`, `se:3.1`, `se:terminal-stability`, `sr:cor` | `airy_blnorm`, `clark_blnorm`, `hb_blnorm`, `airy_stability`, `clark_stability`, `terminal_stability`, `clark_stability_kappa2`, `tendsto_clarkKappa2_atTop`, `hb_stability`, `hbMultiI_expansion`, `hbCommonShift_lt_one`, `se_terminal_stability_boundary`, `hb_blnorm_s`, `airy_blnorm_s`, `clark_blnorm_s`, `cluster_mass_tendsto`, `cluster_position_tendsto`, `crossing_cluster_mass`, `crossing_barycentre_diff_tendsto` | see section 7 rows |
| Fold-tip instances (Paper I's FT) | `ft:FT` | `ft_fixedWeight_all`, `fw_foldTip_hypotheses_all`, `ft_virasoro`, `ft_n1` | C1-C4, C5a-C5c (Airy level) at every `(w,Q)` |
| Five-term constants | `cts:langer`, `cts:phaselock`, `cts:main`, `pm:tip-match`, `cts:tip-shared` | `comb_minimum_virasoro_c0Star`, `g3Out_eq_g3Vir`, `gamma0_eq_gamma0Of_out`, `tip_match`, `airyLinearMoment`, `airyBC_id` | Virasoro |
| Five-term halves (conditional) | `thm:spinless-expansion` | `spinless_upper_of_inputs`, `spinless_lower_of_inputs` | Virasoro, modulo `UpperMainInputs`, `LowerMainInputs`; lower remainder `-C c'^{-1} log c'` (the paper's `cts:lower-main` now has `-C c'^{-1}`) |
| Continuous spin | `spinnotes:S3`, `sd:*` | `spinS3`, `spinDSD`, `spinDA`, `spinDR`, `spinDLP` | `a >= 2` (`c >= 25`) |
| Mixtures, integrality tools/obstruction | `pmix:*`, `int:*` | `MixtureData.pmix_o1_mixture`, `pmix_vac_f1`, `twoSimpleZeroTransfer_src`, `int_closed`, `cheb_explicit`, `int_obstr_a`, `int_obstr_a_primal`, `pmix_duality_common`, `src_sigma_unconditional`, `pmix_o1_component_comparison_unconditional` | see section 7 rows |

## 5. Scope caveats, hypotheses and paper findings

### 5.1 Scope caveats (so nobody cites a Lean statement as the paper's)

- `FixedWeightProblem` is integer `w` with a product `Q`; "every `(w,Q)`" means that class. Real `w`, mixtures and unflavoured
  `N = (2,2)` are outside it.
- `ds:E`: (b) carries the extra hypothesis `0 < T_V` (discharged by `T_V_pos` or the lower bounds); statements over
  `DualSetupCore`; every "has a subsequence" step is along an ultrafilter `<= atTop`; the Laplace-integrability hypothesis of (c)
  is not needed (it follows from `h in L^1(sigma)` via `w_* <= h`). Since PR 299 the paper's `ds:E` attains the reserve at the
  endpoint even with zero residual budget: check `theorem_E_c_reserve` covers that case. `corollary_E1` and `ds:E1` give a
  crossing measure with gap exactly `T_V`; atomicity comes only from `theorem_primal`.
- `ds:primal`: proved at `(H_w)` for every fixed `0 < c~`, `12 S <= c~` (no strip hypothesis; `dsl_strip_fixed_a` is
  `dsl:strip-fixed`(a), without evenness of `G` and real-analyticity of `g` on `(-a',inf)`; (b) is `T_V_pos`, positivity only).
  The paper's class is `(H_{w,lambda})`; common sources and mixtures are `theorem_primal_src`/`_floor`. The clause "real-analytic on `(-a,inf)`" is replaced by what the proof uses
  (`g_*(t) = G(sqrt(3t/c~))`, `G` holomorphic on the strip, locally finite zero set on `[0,inf)`). Since PR 304 the paper adds (b)
  the finite active set `F_act = F ∩ {g_* = 0} ∩ (0, T_F)` with `T_{F_act} = T_F`, and since PR 296 convergence of every
  normalised minimising sequence and (d) inactivity of compact sites where `g_* > 0`; Lean has (a) with `M[g_*] = 1`, (b), (c)
  (locally finite carrier, `nu({T_F}) > 0`), (d).
- `TheoremC15UpperInput prob` is the `O(1)` upper half `T_V <= T_* + D_+`; its name and docstring (`FixedWeight/OptimalMeasure`)
  cite Theorem C15 / `thm:fixed-weight-expansion`, which are five-term statements. It remains a hypothesis of
  `corollary_E1`, `corollary_two_four_of_upper`, `ft_fixedWeight_H3`, whose `_all` instances discharge it.
- `TwoSimpleZeroTransfer prob` is a theorem at every weight (`twoSimpleZeroTransfer_all`); the `_of_T2` forms keep it as a
  hypothesis. `designPropertyP_*`, `Sigma` are for the extremal measures with the far-first-site family omitted (the TeX keeps
  its `f >= 2` Step 6 with an internal note); the Lean designs carry a bump also at `w = 1`.
- `gt:2.1` is for weakly feasible tests (`g_vac >= 0`), not for measures with vacuum slack.
- `windowOptimum*` (`TwoLevel/WindowOptimum*`, 1.7k) proves a qualitative window optimum with decay `K^{-1/15}`; the paper no
  longer states it (the former Proposition 2.3; `pmix:rigidity`(c) is the current statement).
- `wone:ftlfw` (since PR 299) no longer assumes W4 and allows normalised vacuum slack; Theorem W1'(1), W1'(2) and J are its
  corollaries. Lean's `FixedWeightLowerBoundInput`, `theoremFTLFW_W_of_YVFor` have the W4 shape, now a special case.
- Named input structures that are still hypotheses somewhere: `FTH4b` (also the wrong form,
  FT-H4b), `DesignPropertyP` for non-design families, `UpperMainInputs`, `LowerMainInputs` (and the derived `SharpUpperFamily`,
  `LowerPhaseStatement`), and the planned `SpinZEnclosures`. Proved inputs that earlier plans listed: `MehlerOddMomentInput`,
  `BesselI0Asymptotic`, `BesselComplexExpansion`, `SDVAmplitudeInput` (design combs), `ShiftSumEstimate`, `TwoZeroIdealApprox`,
  `DesignTailBounds`, `TwoSimpleZeroTransfer`.
- Spin skeleton: `SpinS22b` as first stated used the Bochner slice integral (0 where the paper's `S_d = infty`), stronger than
  the paper; it is restated with slice integrability (the paper's statement) and proved. Satisfiability of the remaining SPIN-F
  `Prop`s is not checked.
- `teb:quant_c1` normalisation (checked against `G_N := h_N/||h_N||_1`): the Lean target `airyExtremal = -Ai^2/(u-a_1)` is
  normalised by its `L^1` mass (`quantC1C_lo = (2 quantC1Mass)^{-1}`), and `quantC1KappaStar = Ai'(a_1)^2/(16 quantC1Mass)` is one
  quarter of the paper's `kappa_* = |G_N'(a_1)|/4`: weaker, enough for every Lean consumer (they use `kappa_* > 0`). The Clark
  instance's `kappa_*`, `C_1` come from compactness (not the paper's effective constants).

### 5.2 Paper findings

Open (wording or hypotheses the Lean records; no stated result found false):
- `pmix:crossing` (PM.3(b)) asserts `|h_0(-alpha)| <= 2` as a consequence of FW-M; Lean takes it as a hypothesis.
- Proposition T(v): Lean has the lower cutoff `s > -xi_*/eps`, which the paper omits.
- `cts:dth0` is stated in polar form `|b_x|^{1/2} exp(i Dtheta_0)`; the paper's `arg` is the continuous determination, which
  exceeds `pi` once `psi > pi/3` (the principal `arg` would differ).
- The class `H_adm` needs only `|H| = O(|1+z^2|^{-(1-eps)})` for the Cauchy step (the paper's `a_infty > 1/2` is stronger; the
  minimum is unchanged); `comb_regularisation` holds for every `eps` in `(0,1)` with constant `25 alpha_C` (the paper states
  `eps < 1/2`); the Lean route builds `G` with the explicit `R^{-1/2}` factor, avoiding the paper's claim that `R` is outer; the
  uniqueness sentence of Lemma C3(2) is needed only for existence of `G_outer` in the datum's form.
- W-T2w at `w > 1`: the multiplier hooks `1 <= R <= K_b`, `R <= 1 + C'/c'` (`bumpComb_ofReal`) are explicit in Lean and implicit
  in the paper; the statements also carry `0 < eta_*`, and `int Psi_g` is defined as `-g_vac/(2 pi)`.
- *Stale headline remainder (found at `80acaed64`):* `thm:spinless-expansion` and `thm:fixed-weight-expansion`
  (`modular_bootstrap_gap_proof.tex`) and the main-text display at `modular_bootstrap_main.tex` line 120 still state the lower
  remainder `-C_- c'^{-1} log c'`, while `cts:lower-main`, `cts:transfer`, `ctu:main` and the main text at line 1299 state
  `-C_- c'^{-1}` (PR 313). Weaker, not false; the gap-proof statements should be strengthened. Lean's lower half matches the
  weaker headline statements.
- *`cts:rosc-uncond` (1) cites `ctl:pass2`, which follows it:* (1)'s good-circle clause is proved by C7b, input after C7 in
  `constant_term_lower_log.tex`; no circularity (C7b uses only `ctl:dyadic`, the chart and FS.2), but the order reads oddly.
- `ut:T2`/`pmix:rigidity`: the plan used to say only `m <= 2` designs are used downstream; `pmix:rigidity`(c)'s HB taper uses
  `(m_0, m_0-1)` designs, so general `m` is on the HB-level path (section 2.1, W-T2w).

Resolved in the TeX (kept so they are not re-raised): `cts:airy-sum-zero` proof now runs over the true zeros `b_k`; the C11 (3)
proof no longer claims K7 "applies verbatim" (it uses the decay bound of the five-piece deformation, `fwM_of_decay` and the vacuum
identity); `bl:norm` now states the interior condition (`s(T_j)` bounded above), which Lean's `T_j <= Delta_{c'}(-K)` encodes;
FIVE-S: the `min(r^{1/2-j}, (1+x) e^{-pi x})` forms were false at the tip (CORRECTIONS row); PM.1(c) needs the reverse window
`|u_n| <= R => |u_{n'}| <= R+1` (now in the TeX); PM.3(a) does not use `V_mix/K -> lambda({0}) > 0`; K.2(2) and L.4(b) (PR 294);
the false `M_{e^{0.5}}` modulus bound and the K.3 hypothesis beyond `0.015` (PR 290). Checked with no finding: W-P6 (the tail
estimate between `xi_* + r_p` and `xi_* + 1/2` is `c_1` depending on `r_p`, `K_b`), PM-1, PM-2 (normalisations
`F^{(w,1)}/F^{mix} = 1/A(xi_*)`, exponents `2 gamma/3 - 1/6`), `cts:g3-gamma0`, the `int:cheb` filtered constants
(`||V_L||_1 <= 6 pi`, `||K_j||_1 <= 3 pi/N'`, contraction `7/16`, `96 pi < 320`).

### 5.3 Lean targets changed between `0932a6c6f` and `80acaed64`

Applied in the rows above; listed so existing Lean statements are checked against them. (PR 307's changes are applied and no
longer listed; git has them.) Labels: `spinnotes:K3` left the paper; new `sd:spinmoment`, `spinnotes:L3a`, `spinnotes:L8a`; no
label cited by this plan, `THEOREM_MAP.md` or `docs/lean_status.md` disappeared otherwise (`cts:Kedge-signed` is new inside C6).
- *Five-term lower (PR 313), the Lean declarations now weaker than the TeX:* `cts:lower-main`, `cts:transfer` (lower half),
  `ctu:main` (lower half) are `-C_- c'^{-1}` (were `c'^{-1} log c'`); `spinless_lower_of_inputs`, `lowerPhase_of_inputs`,
  `lowerUstar` keep the log (weaker; the labels stay partial). C7 (4) `cts:combined` is `O(c'^{-1} eta_R + c'^{-4/3})` at every good
  radius, with no `1_{E_un}` term and no pass-1 hypothesis; C7 (1) states the good circle `eta(R) <= C c'^{-1/3}` (no first good
  radius `eta(R_1) <= C`); C7b `ctl:pass2` is unconditional with `eta(R) <= C c'^{-1/3}`; C8 `cts:boas` is `>= -O(c'^{-4/3})`; C8a
  `ctl:freeze` is a centre-averaged statement (`O(c'^{-4/3})` after averaging, not per window). The fields `LowerCombined`,
  `LowerPass2`, `LowerBoas` are implied by these (weaker, still true); `LowerFirstGood` and `lowerFirstGood_of_chart_on_band` are a
  proof step of no current statement (`cts:rosc-uncond` partial -> planned); `LowerPassOne`, `lower_pass_upper` and
  `pass2_exponents` belong to the deleted two-pass proof. C6 gains the signed estimate `cts:Kedge-signed` (FS.1); `cts:phic-exp` is
  now derived from FJ (2). Upper side: C10-C15 statements unchanged (the C15 proof now reads the coefficients through FJ (2));
  `UpperMainInputs` unchanged.
- *Unchanged Lean targets:* `thm:spinless-expansion` (still `+-C c'^{-1} log c'`), `thm:fixed-weight-expansion`, all `ctu:*` other
  than `ctu:main`, `cts:edge-hankel`, `cts:smooth-env`, `cts:tip-shared`, `pm:tip-match`, C11-C14, `rem:corL`, `int:*`, `s4:*`,
  `rem:thmOloc`, `spinnotes:S*`, `scal:*`, `sd:*` except a wording pointer in `sd:R` (to SD-M2), every fold-tip statement.
- *Spin:* new `sd:spinmoment` (SD-M2; SPIN-M). Integer spin (PR 311, SPIN-Z only, no Lean yet): K.1 for every `b_t > 0`
  (collar by continuity); K.3 and the explicit real collar moved to the note; K.4 loses its real-collar clause and gains the
  effective coefficient `12 C_1^new` and the trial-radius slit envelope; new L.3a (tip averaging), L.8a (normalised Airy profile,
  sharp-cutoff total-variation limits); L.5 for a bounded cutoff range; L.6 trimmed to the box statement; L.7, L.8 restated.
  `SpinZEnclosures` fields rewritten in row SPIN-Z.
- *Notation and imports:* `kappa_+-` -> `c_0^+-` in the main text (Paper I constant terms; no Paper II Lean name uses it); Paper I's
  TeX no longer imports Paper II (no effect on Lean: Paper I's Lean still imports `ModularBootstrap.FiveTerm.LowerGood*`,
  `LowerDyadic`, `ConcreteBootstrap`).

## 6. Boundary with the Paper I session, and the fold-tip interface

- Paper I owns `SignUncertainty/`, `CohnElkies/`, `TwoEdgeBootstrap/`, `Special/Airy*`, `Complex/`, `Analysis*`, `Asymptotics/`
  (plan `FormalResearch/SignUncertainty/PLAN.md`). Paper II imports `TwoEdgeBootstrap` (`teb_bootstrap_part1`), `Special` and some
  `SignUncertainty` modules (`CtOuterBoundary`, `CtOuterGen` for `FiveTerm/StripOuter*`; `AiryEtaUnfold` for `LowerGoodMain`) and
  edits none of them; if Paper I changes those, `StripOuterGen`, `StripOuterBoundary`, `LowerGoodMain` are at risk. The recalled
  results of 7.10 map to Paper I's Lean there.
- Paper I's M5 plans to refactor the Virasoro `ArcBounds`/`QuadratureBounds` for the Hankel TE.3 instance;
  `FixedWeightBand/BootstrapW*` already generalises them to every weight `w`, and the Hankel instance should start from that
  pattern. Paper II does not refactor `ConcreteBootstrap/` or `TwoEdgeBootstrap/`.
- Langer charts and Mellin strips are separate objects (Paper I: Hankel/Bessel density, `gt:7.7b/c/p`, `SignUncertainty/
  MellinStrip*`; Paper II: Virasoro comb density, `Ramped/LangerTau*`, `FixedWeightBand/Mellin*W`). No duplication.
- **Fold-tip.** Theorem FT is Paper I's (Section 4, `fold_tip_universality.tex`, `fold_tip_two_edge.tex`, `fold_tip_instances.tex`);
  its Lean code is `ModularBootstrap/FoldTip/` because Paper II's instances use it. FT-0..FT-2 are done (import
  `TwoEdgeBootstrap`, edit nothing there; `TwoEdgeBootstrap/FoldTipSeed.lean` serves only Lemma L and is unused). For Paper II's
  instances C1, C2, C3 (`O(1)`), C5a, C5b and C5c are proved by other routes and FT reuses those proofs (no refactor of Prop T,
  Theorem R or `Sigma` through FT: about 8k lines at stake for little gain).
- **Agreed interface** (`SignUncertainty/PLAN.md` section 5): `HermiteBiehlerData` lives in `SignUncertainty/HermiteBiehlerData.lean`;
  the base structure `ChartCompactness` is owned by this lane (FT-CC); its M8 TE.0' is a converter into `ChartCompactness` plus
  the shared rigidity theorem. `ChartCompactness` and its concrete instances are on master: `FoldTip/HankelChartCompactness.lean`
  (Paper I's Hankel multilevel problem; `radialRigidity_to_chartCompactness` converts Paper I's `RadialRigidityPackage` without
  editing `RadialRigidity.lean`; `shellReduction_littleO` is the `o(d^{1/3})` shell reduction at all levels, and Paper I's `O(1)`
  `ShellReduction` still needs M8's all-level `teb_mellin` / `teb_bootstrap_hb`) and `FoldTip/FixedWeightChartCompactness.lean`
  (Paper II's fixed-weight problems). Paper I's `lem:qual-compact` is in Lean (`Analysis/QualCompact`: `qual_compact`,
  `qual_compact_real`); Paper II's `compact_negative_mass` is not re-derived from it (it assumes pointwise convergence off one
  compact set, not local `L^1` convergence); use `qual_compact` for `bl:norm`-type or FT-3..6 needs.
- Paper I does not plan Lemma WP, Lemma WR or `teb:quant_c1_near`; here they are FT-H4b and FIVE-L/FIVE-W.
- **Reverse imports.** Paper I's Lean imports Paper II files: `CtDyadicRadius` imports `FiveTerm/LowerGoodCircle`, `LowerDyadic`;
  `CtDyadicArea` imports `FiveTerm/LowerGoodArea`, `LowerGoodWtilde`; `HankelQuantC1` imports `ConcreteBootstrap/QuantC1Airy`.
  Edit these only in place with their statements kept, and rebuild `FormalResearch.SignUncertainty` after any change.
- **Shared fine-order lemmas (since PRs 312-313).** FS.1 `fs:half-cubic`, FS.2 `fs:circle`, FJ `fj:lemma` are printed once, in the
  Paper I supplement (`CFT/common/fine_order_*.tex`), and both papers' lower proofs use them (Paper II via `\plainpartref` to the
  companion supplement). One Lean copy, phase-free, in a shared file (FS.1 is in `SignUncertainty/FineOrderSigned*.lean`; FS.2 and FJ are
  to follow there or in `Asymptotics/`; record the choice in both plans). FS.2's proof already exists inside Paper I's
  `ct_dyadic_radius`; extracting it and re-deriving `ct_dyadic_radius` is the first step. Paper I's `ct_lower` (master `1e8e81d`) is
  the log form; the shared FS.1 and Paper I's exact-phase Fejér positivity give its log-free form.
- **Five-term lower bound: shared analytic cores** (`SignUncertainty/PLAN.md` section 5, item 7). FIVE-L and Paper I's F1 are
  one mechanism for two phases; phase-free cores have one copy. Here: `LowerBoasResidue` (`boas_residue_zero`,
  `rect_boundary_zero`), `LowerDyadic` (`markov_select`, `dyadic_term_le`), `LowerGoodCircle` (`lowerGoodSet`). Paper I:
  `CtHalfDiscPoisson`, `CtFejer`, `CtSd*` (`sd_eval`), `CtCfu*`, `CtMorse*`, `CtDyadicArea`, `CtDyadicRadius`, `CtScale*`,
  `CtHalfMoment`, and the shared `Complex/HalfDiscCauchy` (`halfDisc_cauchy`), `Complex/HalfDiscMoments`, `Complex/HalfDiscPoisson`
  (upper half-disc; this lane's `FiveTerm/HalfDisc*` is the right half-disc, a different object), `Asymptotics/DyadicAbsorption`.
  Paper I has proved its whole log-form stack (`ct_lower` unconditional; scale-`r` bootstrap `CtScale*`, half-moment
  `hankel_neg_half_moment_le`); since PR 313 Paper II's lower route needs neither the scale-`r` bootstrap nor the half-moment.
  Any new shared core goes to whichever lane needs it first, which records it in both plans.
- **Five-term upper bound (same rule as Paper I's M10).** FIVE-U's exact-CFU geometry (`cts:upper-design`, `cts:shifted-langer`)
  instantiates Paper I's divided-difference chart (`FctCfuTheta.cfu_chart`, `FctHomotopy*`, `FctJCBound`, `FctWeighted`);
  FIVE-L's `cts:cauchy-dual` reuses `CtSd*`, `CtMorse*`, `CtOsc*`, `CtCfu*`.
- TE.0' beyond `alpha = 0`: Paper I's M8 is the Hankel type-(I) instance for polynomial `(P,Q)`; Paper II did the Airy type-(II)
  constant-Clark-pair instance in `ConcreteBootstrap/QuantC1Clark.lean` and does not edit `QuantC1Airy.lean`, which Paper I's
  `HankelQuantC1` imports.

## 7. Coverage by group

One line per group; labels by state are in Appendix A, declarations in `THEOREM_MAP.md`. Files are in
`CFT/modular_bootstrap/paper/`. Rows list only what a Lean citation must not overlook.

### 7.1 Crossing and the lower side
- **CR** (`crossing_sum_rule`; 3 done): `Crossing/`; cite the `_unconditional` forms (`SumRule.lean` originals take the proved
  `MehlerOddMomentInput`). `fw:crossing` allows half-integer `w` since PR 296 (`2w` in `Z`); that case is not in Lean and no
  headline uses it.
- **LB1** (`vlo:Bessel`, `vlo:Gap`, `vlo:PJ` done; `vlo:BesselConst` partial): existential Bessel constants; Lemma G and PJ at every
  `(w,Q)`.
- **LB2** (19 `vlo:*` labels, done): Virasoro and every `(w,Q)` (`FixedWeightBand/`); Proposition L (`vlo:L`) has no standalone
  statement (absorbed in `LemmaQData.bvChoice`, `Contour/VirasoroScaleChoice`).
- **LB3** (`ft:PP`, `vlo:J` done; `wone:ftlfw`, `wone:genlower` partial): integer `w`; `vlo:J` zero slack only;
  `wone:ftlfw` at `m_0 = 1` (Airy) and `m_0 = 2` (Clark pair), and `ft_commonSource_twoEdge` (one level, `(P,Q) = (1,0)`, zero vacuum slack, any `CommonSource`); general `(P,Q)` and real `w`: HB1; `wone:genlower` parts (1),
  (2).

### 7.2 Blow-up, rigidity, weight axioms
- **BL** (`bl:T`, `bl:T1`, `bl:T2`, `bl:T4`, `bl:T5` done; `bl:norm` partial): tests with `g_vac >= 0`; `bl:norm` in the Langer
  `u`-variable and the paper's `s`-variable (`NormLimitSVariable`), with prescribed-node data as hypotheses (SLK rest). Lemma T3 is `lemma_T3_unconditional`.
- **RG** (`rig:R`, done): every `(w,Q)`; `Att` a hypothesis as in the paper.
- **W** (`n1:L4`, `n1:L2` done; `n1:T3`, `n1:T5` partial; `n1:P1` not planned): `n1SuperVirasoroProblem` (weight one). `n1:L2`:
  instance of L4, the comparison `v_2 = 2 pi^4` not stated. `n1:T3`: lower half, `O(1)` law, `Sigma_0`, `Sigma`; five-term:
  FIVE-W. `n1:T5`: items in Lean are the lower bound, `O(1)` law, duality, Clark boundary, `se:3.2`; the rest per its items.

### 7.3 Upper side
- **ESD** (6 done), **CMB** (14 done; `rem:cardy` is the `remarkx` Lemma A_V; `rem:P1.1` closed form `C_* = 4 pi sqrt kappa`,
  decimal numerical), **UTW** (10 done; FW-M at every weight by radial Fourier inversion on `R^{2w}`).
- **UTP** (`ut:II`, `ut:R`, `ut:T` done; `ut:IIF`, `ut:I`, `ut:III`, `ut:Vac` partial): `f = 1` designs at every weight, and
  `(f,r) = (2,1)` at every weight (`twoZeroBump_regionII`, `twoZeroBump_pos_g`, `twoZeroBump_vacuum_core`); general finite real
  factors: W-T2w general `m`. `Upper/Ramped` (the `O(1)` route U*) is not a paper result.
- **T2** (`ut:T2`, `wone:clark` done; `ut:ideal` partial): `ut:ideal` at `m = 2` (`twoZeroIdealApprox`).
- **SR** (`sr:P`, `sr:Sigma0`, `sr:Sigma`, `sr:cor` partial; `sr:single-level` planned): extremal measures (not every measure
  satisfying `Gap`), far-first-site family; `sr:cor`: `1 + o(1)` for the paper's `1 + O(r) + o(1)`, crossing forms take
  `SigmaConclusion` (discharged by `sigma_unconditional_probW`); the barycentre assertion is `ClusterBarycentre`
  (`crossing_barycentre_diff_tendsto`).
- **UP** (no paper label; `pmix:ramped` at one component): done at every weight.

### 7.4 Two-level curve and soft-edge stability
- **TL** (`gt:2.1`, `se:3.2`, `se:3.1`, `se:cdual`, `se:terminal-stability` done; `gt:2.4` (aliases `gt:2.5`, `gt:2.6`), `gt:hb`, `se:3.3` partial): `gt:2.4` partial only for mixtures (PM-3); `gt:hb` at `m_0 = 1, 2` (HB1);
  `se:cdual` done (`se_cdual_fixedWeight`, `_fixedWeight_singleton`, `_floor`, `_common`, `_mixture` in `TwoLevel/ConstrainedDualitySE.lean`: unconditional at every fixed charge in range); `se:3.3` zero and compact offsets (`se_crossing_corollary_offset`) for the two-zero designs; `se:3.1` done (`clark_stability`, `tendsto_clarkKappa2_atTop`);
  `se:terminal-stability` done, all clauses, for fixed strict HB data (`se_terminal_stability_boundary` in `Stability/HbBoundaryCoord`: expansion `se:multilevel-slope` `hbMultiI_expansion`, `b_m > 0`, `I_N > 0` and `se:terminal-slope` (`hb_stability`), boundary chart `Z_m` with signs, `se:hb-boundary-diff`); `se:common-shift` is `hbCommonShift_lt_one`. `theorem_SE7`,
  `theorem_SE7_uniform` are the Virasoro `O(log c')` forms.
- **STAB** (`rem:thmL`, `rem:thmBstab` done; `rem:corL` partial; `rem:thmOloc` planned): `rem:thmBstab` for any entire `L^1`
  `AiryG` of the stated growth, non-vanishing as `exists x, f x != 0`; `rem:corL` = `corL_virasoro` (FIVE-L).

### 7.5 Duality, attainment, infinite-order limit
- **DU** (`ds:D1`, `ds:M`, `ds:E` done; `ds:farkas`, `ds:E1` partial): `ds:farkas` without the symmetry clause, second
  countability in place of the paper's metrizable one-point compactification; `ds:E1` atomicity not combined with
  `theorem_primal` into one statement.
- **PA** (`ds:primal`, `dsl:strip-fixed`, `dsl:one-level-clusters`, `dsl:near-opt-mass` partial; `dsl:hb-clusters`,
  `dsl:hb-mass` planned; `dsl:compact-mass` recalled): section 5.1. `dsl:strip-fixed`(a) done at every fixed charge `12 S <= c~`
  (`dsl_strip_fixed_a`; floor/mixture form `dsl_strip_fixed_a_of_floorAt`), evenness of `G` and analyticity of `g` not stated; (b)
  `T_V_pos`, positivity only. `dsl:one-level-clusters` (a), (b) (`one_level_clusters`) and `dsl:near-opt-mass`/`dsl:D1-exact`/`dsl:d1-asym`
  (`one_level_near_opt_mass`) for `(H_w)` `FixedWeightProblem` only; `b_n = T_V - T_*` is proved `O(1)` and not identified with `c_0^*(w,Q)` (needs FIVE-W `ctu:main`).
- **LP** (`ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact`, `dsl:positive-ray` done; `ds:LP`, `dsl:reserve` partial): `ds:cont`
  for real-analytic `v` (stronger than the paper); `ds:mom`, `dsl:poly-compact` for arbitrary real odd targets
  `|b_k| <= (C_2 k)^k` (`ds_mom_ref`, `poly_compact_ref` the positive-reference corollaries); `ds:LP` at `(H_w)`; `dsl:reserve`
  as `dslReserve`.

### 7.6 Five-term expansion
- **FIVE0** (`cts:langer`, `cts:phaselock`, `cts:main` done; `cts:involution`, `ctu:common-functional` partial; `ctu:piece4`,
  `ctu:jets`, `cts:base-jets` planned): Virasoro only (weight one, `A = 1`). `OuterDatum` records only what `cts:main` uses, with
  the weaker endpoint bound `c <= |G| <= C|1+z^2|^{-5/4}` near `+-i` (`gout_near_I`) in place of the paper's two-sided
  `|1+z^2|^{-1} (log)^{1/2}`; `gout_near_one` is the two-sided `|z-1|^{1/2}` bound; `cts:R-id` holds by construction. Lean's
  jet route (strip coordinate, Poisson slope of `hbarA`, strip-Cauchy identities) does not follow the paper's four-piece
  integration by parts in `y`; both give `g1 = 3 + 6/pi - 16 sqrt2 xi_*` and `g3 = 7 - 18/pi - (16 sqrt2/3) xi_*` (about
  `-0.8459`; the paper's `-0.84562`), `gamma0 = (21 pi - 78 + 8 sqrt2 pi xi_*)/40`.
- **FIVEL** (`cts:edge-hankel`, `cts:lower-main` partial; `cts:rosc-uncond`, `cts:boas`, `cts:cauchy-dual`, `ctl:*` planned):
  section 2.1. `cts:lower-main` (first display) in Lean has `-C c'^{-1} log c'` for the paper's `-C c'^{-1}`.
- **FIVEU** (`pm:tip-match`, `cts:tip-shared` done; `cts:smooth-env`, `cts:transfer` partial; C11-C14 planned): section 2.1.
- **FIVEW** (`ctu:O1`, `thm:spinless-expansion` partial (`thm:spinless-expansion` still states the log on both sides, which
  the conditional Lean halves match); `ctu:main`, `ctu:table`, `ctu:weight`, `ctu:strip`, `ctu:tip-window`,
  `ctu:tip-kernel`, `thm:fixed-weight-expansion` planned).

### 7.7 Positive mixtures
- **PM** (eleven labels partial, five planned). Scopes: `pmix:rebase` (local finiteness of weighted push-forwards a hypothesis;
  `nu_j` on `(0,oo)`, `W_j >= 0` measurable, `n_j > 12 r`; since PR 301 an exact affine push-forward identity); `pmix:weight`
  (atomic `lambda`; the nonnegative-Taylor-coefficient clause of (a) not formalised); `pmix:crossing` ((b) in the abstract form of
  `fwM_of_decay` with `|h_0(-alpha)| <= 2` a hypothesis; the `AdmissibleSpectrum` corollary not ported); `pmix:jets` (only
  `pmix_jets_hyp` and `MixtureData.pmix_jensen`, whose integrability is a hypothesis; since PR 301 the paper's form is an exact
  integrated relative-entropy identity); `pmix:punif` (no separate `-5/2` bound on `G`); `pmix:ramped` (at
  `d = M0 c'^{-1/3}` for each fixed `M0`); `pmix:smooth` (coefficient `1/2` for `3/8`, hypothesis (i) on the whole window, vacuum
  step at `d = M0 c'^{-1/3}`); `pmix:o1` (two-sided for every `CommonSource`, `pmix_o1_lower_common`, `pmix_o1_common`, `pmix_o1_levels_common`; the comparison clause `T_mix >= min_i T_{V,i}(n - 12 r_i)` is `pmix_o1_component_comparison_unconditional` (`0 < c`, `12 Smax <= c`; `pmix_o1_component_strict_gt` is a Lean addition); `pmix:liminf` partial: `pmix_liminf_of_component_c0` is conditional on component lower bounds `hcomp`, the identification with `c_0^*(w,Q_i)` (via `ctu:c0`, `int:strict-weak`) is not formalised; since PR 304 a
  strictness clause, not in Lean); `pmix:vac` (`(1,0)`, `(2,1)`, any common source; second limit one-sided; `g > 0` proved where
  the interface asks `0 <= g`; Lean absorbs the paper's `sqrt(n') lambda^gamma = o(1)` transform step into the window comparison;
  at `f = 1` the lobe is controlled by sign, not the paper's absolute tail bound). Optional: generalise W-P5 in place to sources
  (`VacWindow/VacCore/VacProp` become wrappers); re-derive `Crossing/SumRule` from the ported forms (needs
  `crossingBounds_ofProblem`); general Borel `lambda`.
  `pmix:duality` (`pmix_duality_common`, `pmix_duality_mixture`: `dsl:strip-fixed`, `ds:E`, `ds:primal`,
  `ds:LP` for every `12 S' <= c~`, no strip hypothesis; analyticity clause as for `ds:primal`). `pmix:rigidity` partial: (a)
  `Sigma_0`/`Sigma` and first-node mass for `CommonSource` (`src_sigma_unconditional`, `src_first_node_mass_of_gap`); (b) exclusion at
  zero offset (`src_two_level_exclusion`), vague convergence (`src_theorem_two_six`), atom weight (`src_tendsto_atom_weight`),
  constrained attainment (`src_two_level_constrained_attainment`). Not formalised: `D_2` lower bound, positive-mass existence for
  `A_2 < A_2^*`, offset `R_off`, `pmix:D1` log asymptotic, rebase transfer to the original `n`; (c) is PM-3.

### 7.8 Integrality
- **INT** (`int:int-closed`, `int:shell-inv`, `int:cheb-explicit`, `int:repair-identity` done; `int:obstr` partial and `int:atom` done; `int:repair`,
  `int:sonine` partial; `int:cheb`, `int:reserve`, `int:strict-weak`, `int:hb-reserve`, `int:main`, `int:hb-integer`
  planned). `int:int-closed` for proper metric spaces (the paper's closed `Y ⊆ R^d` is a special case); `int:shell-inv` with the
  cell step a hypothesis (as in the paper's use), Lean stage `j` = paper `k-1`, `nu_Z` a `Measure.sum` (merging coincident atoms
  not formalised); `int:repair-identity` with the existence of `f` from `||P U P|| < 1` a hypothesis; `int:repair` and `int:sonine`: proved at integer weights `w >= 1` only (paper: real `w >= 1`, real `w >= 1/2`), parts (1)-(3) of `int:repair` by `hankel_repair` with constant `sonineRepairConst` (Weber's integral `weber_laplace`, radial Fourier concentration `fourier_concentration_radial`, `hankelSonine_inv` with bound `max 4 (2048 pi^2 B^2 e^{16 pi B})` in place of the paper's constants; the Taylor core is `hankelDual_bound`, `int:Hw-eta` in the `1/m!` form) in `Integrality/{WeberLaplace,SlitMaxMod,FourierConcentration,RadialConcentration,HankelFourier,HankelSonine,RepairHankel}.lean`; `int:atom` done (abstract floor `W`, as in the paper) in `Integrality/{AtomBounds,AtomCell,Atom}.lean` (`int_atom_common`, `int_atom_cheb_explicit`, `int_atom_fixedWeight`); `int:obstr`(a) done at `(H_w)` (`int_obstr_a`,
  `int_obstr_a_primal` in `Integrality/IntegerObstruction.lean`, every fixed charge `12 S <= c~`), mixtures/common sources can now be rerun over PM-4,
  and (b) is INT-S.
- **INTL** (5 not planned). **INTS** (5 planned).

### 7.9 Spin
- **SPINF** (`spinnotes:S21`, `S22`, `S22b`, `S23`, `S24`, `S3`, `scal:C1`, `scal:C3` done; `spinnotes:S1` done to stated skeleton scope with `spinS1a`, `spinS1b`, `spinS1c`, `spinS1d`, `spinS1e`, partial relative to the `T`-invariance remark of S1(a)).
- **SPIND** (eight `sd:*` done, including `sd:spinmoment` with `-limit`, `-ratio`, `-endpoint`, `-pair`; `sd:R` partial: the concentration clause via `dsl:hb-mass`).
- **SPIN4** (all fourteen `s4:*` done: `spinS4_2_1`-`spinS4_6_1`, `spinS4_4_4`, `spinS4` in `Spin/SpinS4*.lean`; the statements of `s4:2.3`, `s4:5.2` and the truncated inverse were corrected to match `spinning_s4.tex`). **SPINZ** (nineteen labels planned, including `spinnotes:L3a`, `L8a`; enclosures as `SpinZEnclosures`).

### 7.10 Results recalled from Paper I (`recalled_paper1.tex`)

Stated in Paper II without proof; they belong to Paper I's plan and Lean, except four whose Lean is in this lane's directories
(`gt:1.0`, `teb:quant_c1`, `teb:kernel`, `teb:mellin`).

| label | result | Lean | status |
|---|---|---|---|
| `ap:thmD` | Theorem D (Airy defect) | `airy_defect_ball`, `airy_defect_bound`, `airyNC_defect_bound` (`Special/AiryCft*`) | formalised |
| `ap:corD1` | Corollary D1 (`nu < -1`) | `airy_quadrature` | formalised |
| `ap:lemH`, `ap:lemHp` | Lemmas H, H' | none (route avoided: `airyQ_sampling` via Fejér-Riesz, `Complex/Hardy*`) | not formalised, not used |
| `ap:lemFR` | Lemma FR | none as stated; Paper II uses `airy_defect_ball_split`, `clark_defect_ball_split_uniform`, `quad_arc_boundClark_uniform` | not formalised as stated |
| `ap:thmQ` | Theorem Q | `airyQ_hasSum_unc`, `airyQ_sampling`, `airyQ_pointwise_sharp`, `airyNC_hasSum_unc` | formalised (1)-(4) |
| `lam:thmB` | Theorem B | `airy_sign_uncertainty`, `airy_sign_equality_iff` | formalised |
| `gt:1.0` | Lemma 1.0 | `clark_good_circle_at`, `clark_good_circle_uniform` (`ConcreteBootstrap/ClarkDiscBoundsUniform`) | formalised |
| `gt:1.0p` | Lemma 1.0' | `airyPQ_good_circle` | formalised |
| `gt:1.0pp` | Lemma 1.0'' | `airyPQ_hasSum_unc`, `airyPQ_lemma44_hasSum` | formalised for `Q != 0` |
| `gt:1.1` | Theorem 1.1 | `airyClark_quadrature`, `airyClark_hasSum_unc` | formalised |
| `lem:hb-uniqueness` | Lemma H.2a | `hb_uniqueness` | formalised |
| `gt:1.2` | Theorem 1.2 | `clark_two_node_uncertainty`, `clark_two_node_equality_iff` | formalised |
| `sr:window-pairing`, `sr:WR` | Lemmas WP, WR | none | FT-H4b (not in Paper I's plan) |
| `teb:quant_c1` | Proposition TE.0 | `teb_quant_c1_typeII` (`ConcreteBootstrap/QuantC1Airy`) | formalised (Airy, type II; constant caveat in 5.1) |
| `teb:quant_c1_near` | Remark TE.0 flat | none | FIVE-L; not needed at Virasoro |
| `teb:quant_c1_hb` | Proposition TE.0' | `teb_quant_c1_clark_typeII`, `_firstLevel` (`m_0 = 2`) | partial: general `(P,Q)` is Paper I's M8 |
| `teb:bootstrap` | Theorem TE.2 | `teb_bootstrap_part1/2/3`, `teb_bootstrap_hb`, `teb_mellin_o1_lower` | formalised |
| `teb:kernel` | Lemma TE.1 | `stripPoisson_representation_symm` (`StripBand/StripPoissonRep`) | formalised (a) |
| `teb:edge-osc` | Lemma TE.1a | `teb_edge_osc` | formalised |
| `teb:mellin` | Proposition TE.3 | `teb_band_reduction`, `teb_band_reduction_quantified` (`StripBand/BandReduction`) | formalised |

## Appendix A. Label index

Every stated result of the paper and supplement at `80acaed64`, by file. Format: state / group: labels (aliases). D done, P partial,
PL planned, NP not planned, R recalled from Paper I. Groups are those of section 7.

**`blowup_limit.tex`** (6)
- D / BL: `bl:T`, `bl:T1`, `bl:T2`, `bl:T4`, `bl:T5`
- P / BL: `bl:norm`

**`comb_estimates.tex`** (9)
- D / CMB: `cmb:K0`, `cmb:K1`, `cmb:K2`, `cmb:K3`, `cmb:K4`, `cmb:K5`, `cmb:K6`, `cmb:K7`, `cmb:K8`

**`constant_term_lower_log.tex`** (3)
- PL / FIVEL: `ctl:dyadic`, `ctl:pass2`, `ctl:freeze`

**`constant_term_slit_strip.tex`** (18)
- D / FIVE0: `cts:langer`, `cts:phaselock`, `cts:main`
- P / FIVE0: `cts:involution`
- PL / FIVE0: `cts:base-jets`
- P / FIVEL: `cts:edge-hankel`, `cts:lower-main`
- PL / FIVEL: `cts:rosc-uncond`, `cts:boas`, `cts:cauchy-dual`
- D / FIVEU: `pm:tip-match`, `cts:tip-shared`
- P / FIVEU: `cts:smooth-env`, `cts:transfer`
- PL / FIVEU: `cts:upper-design`, `cts:regionII-floor`, `cts:shifted-langer`, `cts:upper-vac`

**`constant_term_universality.tex`** (10)
- PL / FIVEW: `ctu:main`, `ctu:table`, `ctu:weight`, `ctu:strip`, `ctu:tip-window`, `ctu:tip-kernel`
- P / FIVEW: `ctu:O1` (`ctu:Airy`, `ctu:c0`)
- P / FIVE0: `ctu:common-functional`
- PL / FIVE0: `ctu:piece4`, `ctu:jets`

**`crossing_sum_rule.tex`** (3)
- D / CR: `fw:abel`, `fw:crossing`, `fw:FWC`

**`dual_spectrum.tex`** (7)
- D / DU: `ds:D1`, `ds:M`, `ds:E`
- P / DU: `ds:farkas`, `ds:E1`
- P / PA: `ds:primal`
- P / LP: `ds:LP`

**`dual_spectrum_limit.tex`** (12)
- D / LP: `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact`, `dsl:positive-ray`
- P / LP: `dsl:reserve`
- R / PA: `dsl:compact-mass` (Paper I `lem:qual-compact`, Lean `Analysis.qual_compact`; Paper II's case `compact_negative_mass`)
- P / PA: `dsl:strip-fixed`
- P / PA: `dsl:one-level-clusters`, `dsl:near-opt-mass`
- PL / PA: `dsl:hb-clusters`, `dsl:hb-mass`

**`edge_transform_sd.tex`** (6)
- D / ESD: `esd:asym`, `esd:hankel`, `esd:global`, `esd:phase`, `esd:lemmap`, `esd:lemma`

**`integrality.tex`** (14)
- D / INT: `int:int-closed`, `int:shell-inv`, `int:cheb-explicit`, `int:repair-identity`, `int:atom`
- P / INT: `int:repair`, `int:obstr`, `int:sonine`
- PL / INT: `int:cheb`, `int:reserve`, `int:hb-reserve`, `int:strict-weak`, `int:main`,
  `int:hb-integer`

**`integrality_lattice.tex`** (5)
- NP / INTL: `int:lat-reserve`, `int:poinc`, `int:amgm-floor`, `int:lat-repair`, `int:int-spin`

**`integrality_spin.tex`** (5)
- PL / INTS: `int:axis-trace`, `int:cheb2d`, `int:cheb2d-explicit` (`int:W0-2d`), `int:cos2d-repair`, `int:cont-spin`

**`lower_o1_two_edge.tex`** (27)
- D / LB1: `vlo:Bessel`, `vlo:Gap`, `vlo:PJ`
- P / LB1: `vlo:BesselConst`
- D / LB3: `ft:PP` (`wone:Q`), `vlo:J` (`int:Jslack`)
- D / LB2: `vlo:S1` (`wone:transfer`), `vlo:S2`, `vlo:S3`, `vlo:S4`, `vlo:S5`, `vlo:S6`, `vlo:XV`, `vlo:J40`, `vlo:J41`, `vlo:J42`,
  `vlo:YV`, `vlo:E2`, `vlo:F`, `vlo:Zp`, `vlo:J7Q`, `vlo:Dp`, `vlo:Z`, `vlo:L`, `vlo:J10escape`
- P / LB3: `wone:ftlfw`, `wone:genlower`

**`n1_super_virasoro.tex`** (5)
- NP / W: `n1:P1`
- D / W: `n1:L2`, `n1:L4` (`wone:weightlem`)
- P / W: `n1:T3`, `n1:T5`

**`positive_mixtures.tex`** (16)
- P / PM: `pmix:rebase`, `pmix:weight`, `pmix:crossing`, `pmix:jets`, `pmix:punif`, `pmix:ramped`, `pmix:smooth`, `pmix:o1`,
  `pmix:vac`, `pmix:duality`, `pmix:rigidity`
- PL / PM: `pmix:main`, `pmix:dominated`, `pmix:floor-criterion`, `pmix:hbphase`, `pmix:hbtap`

**`recalled_paper1.tex`** (22)
- R / REC: `ap:thmD` (`thm:airy-defect`), `ap:corD1`, `ap:lemH`, `ap:lemFR`, `ap:lemHp`, `ap:thmQ` (`thm:airy-quadrature`),
  `lam:thmB` (`ap:thmB`, `thm:airy-threshold`), `gt:1.0`, `gt:1.0p` (`lem:hb-good-circles`), `gt:1.0pp` (`lem:hb-quadrature`),
  `gt:1.1` (`cor:clark-quadrature`), `lem:hb-uniqueness`, `gt:1.2` (`thm:clark-threshold`), `sr:window-pairing`, `sr:WR`,
  `teb:quant_c1` (`prop:airy-local-stability`), `teb:quant_c1_near`, `teb:quant_c1_hb` (`prop:hb-local-stability`),
  `teb:bootstrap` (`thm:strip-feedback`), `teb:kernel` (`lem:strip-poisson`), `teb:edge-osc`, `teb:mellin` (`prop:mellin-feedback`)

**`remainder.tex`** (9, including the `remarkx` Lemma A_V)
- D / CMB: `rem:P1.1`, `rem:P1.2`, `rem:analytictip`, `rem:analyticII`, `rem:cardy`
- PL / STAB: `rem:thmOloc`
- D / STAB: `rem:thmL`, `rem:thmBstab`
- P / STAB: `rem:corL`

**`rigidity.tex`** (1)
- D / RG: `rig:R`

**`soft_edge_two_level_stability.tex`** (5)
- D / TL: `se:3.2`, `se:3.1`, `se:cdual`, `se:terminal-stability`
- P / TL: `se:3.3`

**`spectral_rigidity.tex`** (5)
- P / SR: `sr:P`, `sr:Sigma0`, `sr:Sigma`, `sr:cor`
- PL / SR: `sr:single-level`

**`spinning_calibration.tex`** (2)
- D / SPINF: `scal:C1`, `scal:C3`

**`spinning_airy_moment.tex`** (1)
- D / SPIND: `sd:spinmoment` (`sd:spinmoment-limit`, `-ratio`, `-endpoint`, `-pair`)

**`spinning_dual.tex`** (8)
- D / SPIND: `sd:M`, `sd:P`, `sd:SD`, `sd:W`, `sd:V`, `sd:A`, `sd:LP`
- P / SPIND: `sd:R`

**`spinning_foundations.tex`** (7)
- D / SPINF: `spinnotes:S21`, `spinnotes:S22`, `spinnotes:S22b`, `spinnotes:S23`, `spinnotes:S24`, `spinnotes:S3`
- P / SPINF: `spinnotes:S1` ((a), (b), (c), (d), (e) all proved to stated skeleton scope; `T`-invariance remark of (a) omitted)

**`spinning_integer_exact_slope.tex`** (4)
- PL / SPINZ: `spinnotes:K1`, `spinnotes:K2`, `spinnotes:K4`, `spinnotes:K4a`

**`spinning_integer_liouville.tex`** (13)
- PL / SPINZ: `spinnotes:L0a`, `spinnotes:L0b`, `spinnotes:L1`, `spinnotes:L2`, `spinnotes:L3`, `spinnotes:L3a`, `spinnotes:L4`,
  `spinnotes:L5`, `spinnotes:L6`, `spinnotes:L7`, `spinnotes:L8`, `spinnotes:L8a`, `spinnotes:L9`

**`spinning_integer_overview.tex`** (2)
- PL / SPINZ: `isl:main`, `isl:finite`

**`spinning_s4.tex`** (14)
- D / SPIN4: `s4:S4`, `s4:4.4`, `s4:2.1`, `s4:2.2`, `s4:2.3`, `s4:2.4`, `s4:3.3`, `s4:3.4`, `s4:4.1`, `s4:4.2`, `s4:4.3`, `s4:5.1`,
  `s4:5.2`, `s4:6.1`

**`upper_transfer.tex`** (20)
- D / UTW: `ut:Z`, `ut:P`, `ut:Phi`, `fw:FWM`, `fw:SDp`, `ut:W`, `ut:ID`, `ut:G`, `ut:V` (`uc:V`), `ut:E`
- D / UTP: `ut:II`, `ut:R`, `ut:T`
- P / UTP: `ut:IIF`, `ut:I`, `ut:III`, `ut:Vac`
- D / T2: `ut:T2`, `wone:clark`
- P / T2: `ut:ideal`

**`virasoro_two_level.tex`** (3)
- P / TL: `gt:hb`, `gt:2.4` (`gt:2.5`, `gt:2.6`)
- D / TL: `gt:2.1`

**`modular_bootstrap_gap_proof.tex`** (2)
- P / FIVEW: `thm:spinless-expansion`
- PL / FIVEW: `thm:fixed-weight-expansion`

Files with no stated result: `modular_bootstrap_main.tex`, `five_term_roadmap.tex`, `spinning_airy_moment_proof.tex`,
`spinning_integer_poincare.tex`, `spinning_integer_multipliers.tex`. Totals: 264 results; done 125, partial 51, planned 59, not
planned 6, recalled 23 (counted from the rows above).

## Appendix B. Calibration (lines of Lean under `FormalResearch/ModularBootstrap/`, `master` `7d1ee0f`)

| directory | lines | directory | lines |
|---|---|---|---|
| `Upper/` (Ramped 21.1k, Window 14.8k, Holes 11.1k, Comb 10.7k, Saddle 8.6k, Hankel 4.8k, Assembly 4.8k, Positivity 4.5k, Rigidity 4.2k, Membership 3.6k, Design 3.5k, Bump 2.3k) | 93.9k | `FiveTerm/` (112 files) | 45.1k |
| `Spin/` (27 files; SPIN-F and SPIN-D) | 28.1k | `FixedWeightBand/` | 19.4k |
| `TwoLevel/` (86 files) | 18.0k | `Contour/` | 12.5k |
| `ConcreteBootstrap/` | 11.4k | `Mixtures/` (31 files) | 8.9k |
| `Blowup/` | 7.8k | `Crossing/` | 7.5k |
| `PoissonJensen/` | 7.2k | `FixedWeightTip/` | 6.7k |
| `Duality/` (with `Primal/`) | 6.5k | `ChartGeometry/` | 6.4k |
| `Chart/` | 6.3k | `WeightAxioms/` | 5.4k |
| `SlitStrip/` | 4.7k | `LP/` | 4.4k |
| `StripMultiplier/` | 3.8k | `StripBand/` | 3.6k |
| `Integrality/` | 3.6k | `ComplexBessel/` | 2.9k |
| `FixedWeight/` | 2.9k | `TipFront/` | 2.7k |
| `FoldTip/` | 2.5k | `Bessel/` | 2.0k |
| `Stability/` | 1.5k | `Rigidity/` | 1.4k |
| `Mellin/` | 1.0k | `Integration/` | 0.5k |
| total `ModularBootstrap/` | 329k | | |

Other: `TwoEdgeBootstrap/` 4.0k, `Special/Airy*` 47.9k (Paper I).
