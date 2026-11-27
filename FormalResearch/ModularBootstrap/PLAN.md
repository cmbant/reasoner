# Paper II (modular bootstrap at large c) — Lean plan

**Source.** QIprojects `CFT/modular_bootstrap/paper/` at `origin/main` `0932a6c6f` (merge of PR 307, 2026-11-27; the plan
includes PRs 299-304 and 307). Master file `airy_scale_core.tex`, supplement `modular_bootstrap_supplement.tex`; Lemma
U* is in the note `CFT/notes/n2_ramped_comb.tex`. Section 5.3 lists what PR 307 changed for the Lean targets.

**Lean.** reasoner `master` `7d1ee0f`; the last ModularBootstrap change is `e94014d` (2026-11-26, SPIN-D complete). **Nothing is
running**: the formalising agent has stopped, and every package marked open below is unstaffed. Umbrella
`FormalResearch.ModularBootstrap`; declaration map: `THEOREM_MAP.md` (section "Modular Bootstrap" and the `Upper/`, `FoldTip/`,
`TwoLevel/` sections after it); reader-facing status: the Paper II section of QIprojects `docs/lean_status.md`.

This file says what is true now; git holds its history. Nothing is claimed formalised that is not on `master`, and a `.lean` file
existing is not verification. Under `FormalResearch/ModularBootstrap/` there is no proof placeholder, no `axiom` and no
`native_decide`; every headline named here has a `#guard_msgs` / `#print axioms` guard pinning `[propext, Classical.choice,
Quot.sound]` (re-checked 2026-11-27 for the declarations of section 4).

**Where things stand.**
- *Lower and upper `O(1)` law, every integer `(w,Q)`:* `Delta_best = c'/Lambda_V + A_opt c'^{1/3} + O(1)` two-sided, no hypothesis
  (`fixedWeightLowerBoundInput_of_problem`, `theoremC15UpperInput_probW`); the design side (Proposition V, Lemma T, Property (P),
  `Sigma_0`, `Sigma`), the fold-tip instances and Corollary 2.4(a) at every weight; T2, Theorems 2.5, 2.6, `wone:clark`(c) and
  `se:3.3` (zero offset) at every weight for the two-zero designs `(f,r) = (2,1)`.
- *Duality:* `ds:E` (a), (b) compact `F`, (c) at every `(w,Q)`; `ds:primal` for `c~ >= c_0(w,Q)` (below `c_0` modulo
  `FixedChargeStrip`); Theorem LP (`ds:LP` (i)-(iii) at `(H_w)`) with `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact`.
- *Five-term expansion (headline 3):* all Virasoro constants are read off the outer function (`c0Star`, `gamma0`, `d2Star`); both
  halves of `thm:spinless-expansion` are proved **modulo named input structures** (`UpperMainInputs`: fields C11-C14;
  `LowerMainInputs`: fields `chart`, `combined`, `pass2`, `boas`), so the expansion itself is not yet a Lean theorem.
- *Spin (headline 1):* the continuous-spin slope `spinnotes:S3` is unconditional (`spinS3`); SPIN-F is done except
  `spinnotes:S1` (a), (d), (e), `scal:C1`, `scal:C3`; seven `sd:*` labels of `spinning_dual.tex` are done and `sd:R` is partial
  (its concentration clause, added by PR 307, needs `dsl:hb-mass`). The sharp
  coefficient `s4:S4` (SPIN-S4), integer spin (SPIN-Z) and the integrality theorems (INT-1 onwards) are not started.
- *Mixtures (headline 4):* PM-0, PM-1, PM-2 in Lean to stated scopes (all partial). *Integrality:* tools INT-T only.

**Counts** (recounted 2026-11-27 against the TeX at `0932a6c6f`). 262 stated results: 259 `result` environments, the
`theorem` and `corollary` of `modular_bootstrap_gap_proof.tex`, and Lemma A_V (`rem:cardy`, a `remarkx`); several labels on one
result are one row. State on `master`: **104 done, 49 partial, 80 planned, 6 not planned, 23 recalled from Paper I**
(22 in `recalled_paper1.tex`, mapped in 7.10, and `dsl:compact-mass`). Appendix A has every label. The previous count (252) did not
classify eight labels present in the TeX; they are now classified: `dsl:positive-ray`, `int:cheb-explicit`, `int:repair-identity`
(done), `cts:base-jets`, `ctu:tip-window`, `ctu:tip-kernel`, `int:hb-integer`, `int:cheb2d-explicit` (planned).

*Counting rule.* A label moves only when its row says so and its whole statement changes class. A general-`m` or general-factor
part still open, a statement proved in a different variable, or one proved under a hypothesis the paper omits keeps it partial or
planned; a proved proof step that is not part of the statement moves nothing (`cts:boas` Step 3, `ctu:jets` at Virasoro,
`ctl:dyadic`/`ctl:pass2`/`ctl:freeze` exponent bookkeeping). Calls that need the rule spelled out:
- *Partial, modulo a named hypothesis:* `cts:transfer`, `thm:spinless-expansion`, `cts:lower-main` (first display only);
  `cts:rosc-uncond` (the first good radius of (1), at Virasoro, from the `chart` field; (2)-(4) are not Lean statements);
  `pmix:rebase` (local finiteness of the push-forwards).
- *Partial, special case or weaker form:* `spinnotes:S1` ((b), (c) proved; (a), (d), (e) stated as `Prop`s); `ds:LP` (`(H_w)`
  only; the paper states the dominated class `(H_{w,lambda})`, mixtures are PM-4); `dsl:reserve` (the `d = 2` swap-invariant form
  `dslReserve` only); `cts:smooth-env` (all three parts at Virasoro; stated for general `(w,Q)` outer functions);
  `cts:edge-hankel` ((1) at Virasoro, the Bessel input of (2)); `ctu:common-functional` (Virasoro data); `cts:involution` (weaker
  endpoint bound near `+-i`); `bl:norm` (Langer `u`-variable); `pmix:smooth` (coefficient `1/2` for the paper's `3/8`);
  `pmix:vac` (`(1,0)`, `(2,1)`, one-sided limit); `pmix:punif`, `pmix:ramped`, `pmix:o1`, `pmix:weight`, `pmix:crossing`,
  `pmix:jets`, `int:repair`, `se:3.1`, `se:3.3`, `se:terminal-stability`, `sr:cor`, `ds:farkas`, `ds:E1`, `dsl:strip-fixed`,
  `ds:primal`, `rem:corL`, `sd:R` (`spinDR` proves the Airy law of the dimension marginals; the `dsl:hb-mass` concentration
  bounds are not in Lean), `sr:P`, `sr:Sigma0`, `sr:Sigma`, `ctu:O1`, `ut:ideal`, `ut:IIF`, `ut:I`, `ut:III`, `ut:Vac`,
  `gt:2.4`-`gt:2.6` (the missing part is named in each row).
- *Planned although Lean has a related object or step:* `s4:2.1` (Lean has the `(log n)^{2/3}`-scale localisation
  `spin_tip_localisation_quad`, not `C_p n^{-p}` for every `p`); `ctu:jets`, `ctu:piece4` (Virasoro jets only); `int:cheb` (Lean
  has the floor `8 N^{5/2}` of `int:cheb-explicit`, not `640 N^2`); `cts:boas` (Step 3 core only).
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
| **3** | **Five-term expansion** `thm:fixed-weight-expansion`, `thm:spinless-expansion`: `Delta_best = c'/Lambda_V + A_opt c'^{1/3} + c_0^* + c_1^Langer c'^{-1/3} + d_2^* c'^{-2/3} + O(c'^{-1} log c')`, two-sided | **Weaker.** `O(1)` law at every `(w,Q)` (above). Virasoro constants complete (FIVE-0). Virasoro expansion proved modulo `UpperMainInputs` (`spinless_upper_of_inputs`) and `LowerMainInputs` (`spinless_lower_of_inputs`); satisfiability of neither structure is checked. Nothing at general `(w,Q)` | FIVE-U, FIVE-L (fields), then FIVE-W |
| **2** | **Extremal spectrum**: attainment and atomicity (`ds:primal`), Airy clusters (`sr:Sigma`, `sr:cor`, `sr:single-level`), Clark curve (`gt:2.1`, `gt:2.4`-`gt:2.6`) | **Weaker or special.** `Sigma_0`, `Sigma` for the extremal measures at every weight (paper: any measure satisfying `Gap`); `gt:2.1` matches; `gt:2.5`, `gt:2.6`, `ut:T2`, `wone:clark`(c) at every weight for two-zero designs; `ds:E` done; `ds:primal` at large charge; `sr:cor` cluster masses and positions (no barycentre); nothing for `sr:single-level` | SR-COR, PA1 (small charge), PA2; DU-F |
| **4** | **Universality across chiral algebras**: fixed weight (`n1:T5`), `N = 1` (`n1:T3`), positive mixtures (`pmix:main`), prescribed HB levels (`gt:hb`) | **Partly.** `O(1)` law and duality at every `(w,Q)`, `N = 1`; `bl:norm` for any `HermiteBiehlerData` (`hb_blnorm`, `u`-variable); stability slopes (Airy, Clark, abstract terminal); mixtures PM-0..PM-2 partial. Five-term, mixture rigidity, general HB levels: none | PM-4, PA2, FT-H4b, then PM-3, INT-2HB, HB1, PM-5; five-term at `(w,Q)` via FIVE-W |
| **1** | **Spin does not help**: continuous spin (`s4:S4`, `spinnotes:S3`, `sd:R`), integer spin (`isl:main`), finite-order programmes (`isl:finite`); integrality shifts the spinless optimum exponentially little (`int:main`) and by `O(log c')` with continuous spin (`int:cont-spin`) | **Partly.** `spinnotes:S3` unconditional (`spinS3`: `(c-1)/Lambda_V - C (c-1)^{1/3} log(c-1)^{2/3} <= Delta_L <= Delta_spin <= Delta_best <= (c-1)/Lambda_V + A_opt (c-1)^{1/3} + C_+`); `sd:*` done except the `dsl:hb-mass` concentration clause of `sd:R` (`spinDR`). The sharp `-O(log c')` coefficient `s4:S4`, integer spin and integrality theorems: none (INT-T tools only) | SPIN-F rest, SPIN-S4, then INT-S, SPIN-Z; INT-4, INT-1, INT-2, INT-3 |

### 1.1 Next steps per headline, smallest first

Each step names its inputs. "Check" marks a question to settle before writing Lean.

**Headline 3 (five-term).** The remaining work is the analytic estimates behind the two input structures, about 40-55k lines.
1. *FIVE-L reuse audit (S, design note only).* Paper I's F1 has since proved most of the same mechanism for the Hankel phase
   (`SignUncertainty/CtBoas*`: `ct_boas_concrete`; `CtDyadic*`, `CtBandTop.ct_dyadic_radius_proved`,
   `CtDyadicCombined.ct_dyadicInputs_of_pieces`; `CtRosc*`: `ct_rosc_book`; `CtDualId*`, `CtChart*`, `CtCfu*`, `CtSd*`;
   `CtLowerFinal.ct_lower` is modulo `CtLowerInputs.dyadic` only). Map each `LowerMainInputs` field to its Paper I analogue
   (`boas` <-> `ct:boas`; `pass2`, `ctl:dyadic` <-> `ct:dyadic`; `combined` <-> `ct:rosc`/`ct:combined`; `chart` <->
   `ct:dual-id`, `ct:cfu`), mark which Paper I declarations are phase-free (reuse as they are) and which need a Virasoro-phase
   instance, and record it in `FiveTerm/FIVEL_DESIGN.md`. This lane already imports `SignUncertainty.AiryEtaUnfold`
   (`airy_eta_le_arcs` re-derives `lowerFirstGood_eta_le`).
2. *`cts:edge-hankel` (2) (S-M):* assemble the statement from `besselI0C_two_term` and the three-term `V(t(x))` expansion.
3. *FIVE-U C14 `cts:upper-vac` (2-4k):* vacuum sum over the Airy window and band, `x_split` cancelling, `tip_match` as input; the
   field `c14_vacuum` (`cts:Vc-exp`).
4. *FIVE-L field `boas` (`cts:boas` Steps 1-2, C8):* Step 3 is `LowerBoasResidue`; port the Paper I `ct:boas` route (finite
   Fejér inequality `ct:fejer`, `CtFejer`), Gaussian-window bounds are in `LowerDyadic`.
5. *FIVE-U C12 `cts:regionII-floor` (4-6k):* hole comparison, Euler product for pairs `k = n +- m`, monotonicity of
   `|T_{chi+i eps}|^2` in `eps` (reuse `Upper/Comb/Factors.blaschkePairQ_mono_eps`, `Upper/Bump/PairFactor`), trigonometric
   phase-error positivity, `C_buf = 4(C1+C2)+1`; builds on `Upper/Holes` K4-K6. Field `c12_regionII`.
6. *FIVE-L field `chart` (`cts:cauchy-dual` (1) with `cts:phic-exp`, C6):* first the `b <-> z` transport `w = cosh(pi b)`,
   `z = zeta_D(b)`, then the CFU/steepest-descent stack for the Virasoro phase (Paper I's `sd_eval`, `outer_band`, `stat_phase`,
   `morse_expansion`, `scalar_ift`, `CtSd*`, `CtMorse*`, `CtCfu*`/`FctCfuTheta`). Step 2 uses FIVE-S (done).
7. *FIVE-L fields `combined` (`cts:rosc-uncond` (4), C7) and `pass2` (`ctl:pass2`):* depend on `chart`, Theorem D, good circles
   and the quadrature in `ConcreteBootstrap`; `ctl:dyadic`, `ctl:freeze` enter here (their exponent arithmetic is `LowerDyadic`).
   `ctl:pass2` averages over the good-phase set `|sin(2/3 r^{3/2} + pi/4)| >= 1/sqrt2` of `ap:E2` (the Lean
   `lowerGood_circle_of_phase` covers a positive-density subset, enough).
8. *FIVE-U C13 `cts:shifted-langer` (5-8k):* exact-CFU shifted Langer identity with the global tip kernel, the `W_D^tip` bounds,
   `Pi_n` asymptotics, a good Airy radius, Region-I positivity; instantiate Paper I's divided-difference chart
   (`FctCfuTheta.cfu_chart`, `FctHomotopy*`, `FctJCBound`, `FctWeighted`), not a second CFU stack. Field `c13_regionI`.
9. *FIVE-U C11 `cts:upper-design` (6-10k):* needs K7 with an amplitude/envelope: `InnerCombHyp` demands `|B| <= 1` and `|B| = 1`
   on `E_+`, which `E_delta B_D` does not satisfy, so write amplitude-carrying copies of `Upper/Membership`, `Saddle`, `Hankel`
   (not in place). Fields `c11_membership`, `c11_first_site`.
10. *FIVE-W (5-8k if FIVE-L/U stay stated over general data):* `ctu:main`, `ctu:O1` (`c_0^*(w,Q)` clauses), `ctu:table`,
    `ctu:weight`, `ctu:strip`, `ctu:tip-window`, `ctu:tip-kernel`, `thm:fixed-weight-expansion`. FIVE-U is already stated over
    any `ShiftSource` and `OuterDatum`; check how much of FIVE-L's `LowerMainInputs` is Virasoro-specific before starting.

**Headline 2 (extremal spectrum).**
1. *SR-COR barycentre (S):* `(t_2 bar - t_1 bar) c^{-1/3} -> c_*(|a_2| - |a_1|) = 0.20705` from `cluster_mass_tendsto` and
   `cluster_position_tendsto` by a weighted average.
2. *SE3 offset form of `se:3.3` (S):* `t_1 = xi_bar n + A_1 n^{1/3} + e_n` with the `L_J(e_n)_-` loss, via `A2star_lipschitzOn`.
3. *SLK `s`-variable form of `bl:norm` (S):* convert `chartUT` by `position_identity` (`SpectrumCorollary`).
4. *STAB (S-M):* second assertion of `se:3.1` (`kappa_2(u_1) -> (2 L_*^{(0)})^{-1}` as `u_1 -> infinity`, from the
   `clark_stability` slope formula and the Airy limit of `||g_alpha||_1`); then a concrete HB instance of `se:terminal-stability`
   (`TerminalData` from `airyPQ_hasSum_unc` with weight `D(tm)/N'(tm)^2`, trial `W = -dslope G tm`, nonemptiness from
   `airyTrial`; the slope form needs `G'(tm) = -N'^2/prod`); the paper's multilevel form (`I(h) = sum b_i h_i + o(|h|)`, local
   HB boundary `Z_m(y)`, `dZ_m/dy_i = -b_i/b_m`) after that.
5. *DU-F `se:cdual` (S-M):* compact-`F` constrained duality with attainment, atom at `T_F`; from DU-G and `theorem_primal`
   (large charge).
6. *PA2, cluster part (M-L):* `dsl:one-level-clusters`, `dsl:near-opt-mass` need only the `O(1)` law, PA1, W-P5; the exact first
   atom and `sr:single-level` need `c_0^*` (FIVE-W).
7. *PA1 blocker (M-L):* `dsl:strip-fixed`(a) for `12 S <= c~ < c_0` needs fixed-charge asymptotics `V/K -> D_0 > 0`; first step
   `K_a <= C V` at fixed charge, then `testClass_integral_kernelK_le` at fixed `c'`. Removes `FixedChargeStrip` from
   `theorem_primal`.

**Headline 4 (universality).**
1. *PM-4 `pmix:duality` (S-M), now unblocked* (PM-0, DU-G, LP1 in; PA1 at large charge): first build the DU-G input
   `DualSetupCore` (and `FixedWeightProblem`-free versions of the LP1 inputs) from a `CommonSource`, then instantiate `ds:M`,
   `ds:E`, `ds:primal`, `ds:LP`.
2. *FT-CC (M, no open parent):* the base structure `ChartCompactness` (section 6); also wanted by Paper I's M8 (its
   `HbMultilevelInputs.lower` docstring routes TE.0' through it). Not on master yet (no declaration of that name).
3. *PM-1 signed-source lower half of `pmix:o1`:* first check whether the slack form of `wone:ftlfw` (since PR 299 it allows
   `int g V <= C_vac c'^{-1/3} M[g]`, no W4) gives it directly; otherwise rerun Theorem W1'(1) (`theoremFTLFW_W_of_YVFor`) against
   `SourceUniformAxioms`.
4. *PM-0b (M, 2-3k):* `ctu:jets` at a general amplitude, hence `pmix:jets` (the input of `pmix:main` through `ctu:c0`).
5. *PM-2 consumer ports (S-M):* `designPropertyP_of_comb` and `toEventual` to `SrcEventualCombData`/`SrcTwoZeroTransferData`
   (no `CrossingSequence` analogue for sources yet); needed by PM-3.
6. *FT-H4b (M-L)*, then PA2 (HB forms), PM-3, INT-2HB, HB1, PM-5 in that order (section 2.3).

**Headline 1 (spin, integrality).**
1. *INT-4 `int:obstr`(a) (M):* inputs `int_closed`, DU-G, `fw:crossing`(1) (all done); the "iff" needs PA1 (large charge is
   enough at large `c`).
2. *SPIN-F rest (S-M each), inputs of SPIN-S4:* `scal:C1` (cited 18 times by `spinning_s4.tex`), `scal:C3`, and the parts of
   `spinnotes:S1` (a), (d), (e) that `spinning_s4.tex` uses; `rem:thmOloc` (elementary: `E = g'^2 + x g^2`, `Ai(0)`, the DLMF
   9.7.15 lobe bound) is also cited there.
3. *SPIN-S4 skeleton (S):* state the 14 `s4:*` targets as `Prop`s and `s4:S4` modulo them (as the SPIN-F skeleton did); inputs
   also `bl:T1`-`bl:T5`, `rem:thmL`, `lam:thmB`, `sd:SD` (all done). Then the lemmas in dependency order (L, 25k+).
4. *INT-1 `int:atom` (M-L):* the abstract floor `W(M) = 8 (M+1)^{5/2}` of `cheb_explicit` and `shell_inv`; moment order
   `M_k >= K H_k / log P_k`.
5. *INT-2 `int:reserve`, `int:strict-weak` (M-L) at `(H_w)`, lower half first:* in the TeX, INT-2 is the canonical case
   `m_0 = 1` of `int:hb-reserve`. Its lower bounds (a)-(c) at `m_0 = 1` use only `bl:norm`(b) (SLK: `airy_blnorm`, `u`-variable;
   check that its conclusion gives the local `C^1` and `L^1` convergence used, `C^1` following from locally uniform holomorphic
   convergence), the `O(1)` law (`u_n(T) -> a_1`), `fw:crossing`(1) and `ds:E`(c) (`theorem_E_c_reserve`, with the variational
   formula `int:reserve-var`); state them as a `lower` conjunct. The matching upper bounds (the sharp law `int:hb-res-sharp`,
   since PR 307) need a fixed design transferred by `pmix:vac` (at `(H_w)`: the W-P5 design side), `ut:ideal`(a) for the
   `m_0 = 1` window family (check against Lean's `m = 2` `twoZeroIdealApprox`), and a weak extremal `g_*` from `ds:primal` with
   `g_*(B_n) = 0` and the cluster input `dsl:hb-clusters`/`dsl:one-level-clusters` (PA2); they are the `upper` conjunct. The
   mixture clause adds `pmix:rebase`, `pmix:o1`; the dominated-source clause waits for PM-5 (`pmix:dominated`).
6. *INT-3 `int:main` (M):* the integer-gap bound needs INT-1, INT-2 (lower half), INT-T, W-P6; since PR 307 the statement also
   has the cluster-mass equivalents in fixed Airy windows and the exponential concentration `|t - t^*_{k,n}| <= e^{-alpha n}`
   (`alpha < L(xi_*)` for `k = 1`, `< L(xi_*)/2` for `k > 1`), via `dsl:one-level-clusters`, `dsl:hb-mass` (PA2); the
   five-term corollary needs FIVE-W.
7. *SPIN-Z, INT-S* after SPIN-S4 (section 2.1).

## 2. Work packages

### 2.1 Open packages

Listed by headline. "Needs" names packages or labels whose Lean is not yet sufficient; done inputs are named where useful.

**FIVE-L** (headline 3; L, 25-30k, about 5k done). Closes `cts:edge-hankel`, `cts:cauchy-dual`, `cts:rosc-uncond`, `cts:boas`,
`cts:lower-main`, `ctl:dyadic`, `ctl:pass2`, `ctl:freeze`; inputs `rem:corL`, `rem:thmOloc`, `teb:quant_c1_near`.
- *In Lean* (`FiveTerm/Lower*`, design `FiveTerm/FIVEL_DESIGN.md`): `corL_virasoro` (`rem:corL` at Virasoro: (a) type-II
  envelope, (b) via `quantC1B2_secant_lower`, (c) `QuantC1B2Holds`, (d) `u_T - a1 <= K c'^{-1/3}`, stronger than the paper's
  `c'^{-1/3} log c'`; the `C^1`-convergence clause of (c) is not exported; constants are Lean's `quantC1*`); `c0Star_neg`;
  `dimension_ge_of_phase_ge`, `delta_best_ge_of_phase`, `spinless_lower_of_phase` (modulo `LowerPhaseStatement`, gp:L);
  `edge_hankel_one_virasoro` and companions (`cts:edge-hankel` (1); `G` is the defined Hankel integral, Hankel inversion is not
  formalised); `besselI0C_two_term` (`||I_0(w) - e^w/sqrt(2 pi w)(1 + 1/(8w))|| <= 70 e^{Re w}|w|^{-5/2} + 2` for `Re w >= 1`; the
  additive `2` is why the downstream form needs `v <= e^{kappa c'}`); `boas_residue_identity`, `boas_local_lower`,
  `boas_residue_zero`, `rect_boundary_zero` (`cts:boas` Step 3); `markov_select`, `dyadic_term_le`, `pass2_exponents`,
  `top_edge_exponent`, `gauss_window_exponents` (bookkeeping only).
- *Skeleton:* `LowerMainInputs prob c0 gamma0` (data `Gout`, `phi`, `uhat`, `c1` with `0 < c1`, `10 c1 <= virasoroBVChoice`)
  over concrete objects (`lowerF`, `lowerH`, `lowerPNodes`, ...), fields `chart` (`cts:cauchy-dual` (1) + `cts:phic-exp`),
  `combined` (`cts:rosc-uncond` (4): the dual identity, (4a) with the `c^{-1}` term, (4b) under the pass-1 hypothesis), `pass2`
  (`ctl:pass2`), `boas` (`cts:boas`); fields quantify over thresholds in the band `T <= Delta(-A_thr)`, the out-of-band case is
  in `lowerPhase_of_inputs`. Proved: `lower_pass_upper`, `lowerUstar_phase`, `lowerPhase_of_inputs` (with `LowerPrelim` and
  `c0 < 0`), `lowerPhase_virasoro`, **`spinless_lower_of_inputs`**. Discharged fields: `firstGood` (`cts:rosc-uncond` (1),
  `lowerFirstGood_of_chart_on_band`, `FiveTerm/LowerGood*`) and `langer` (`lowerLangerPhase_holds`, `FiveTerm/LowerLangerBridge`:
  `tauPhase(sqrt(3 Delta_c(u)/c)) = -u/(betaTip c^{2/3})` on the real band). Satisfiability of `LowerMainInputs` is not checked.
- *Open:* the four fields (section 1.1 steps 1, 4, 6, 7), `cts:edge-hankel` (2), `cts:lower-main`'s second display (in `c`).
  `teb:quant_c1_near` is not needed at Virasoro (`c0Star < 0` gives `phi_c(a1) > a1`, so the violator form suffices); FIVE-W may
  need it (a copy-adapt of `QuantC1Airy` in a new file, about 1.3k; `QuantC1Airy` is imported by Paper I and is not edited).
  `rem:thmOloc` is not needed here (it is an input of SPIN-S4).

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
- *Open:* C11-C14 (section 1.1 steps 3, 5, 8, 9).

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

**PA1, rest** (headline 2; M-L). `dsl:strip-fixed`(a) for `12 S <= c~ < c_0` (section 1.1, headline 2, step 7). Also not
exported: local-holomorphic convergence of `G_j` (proved internally); not stated: atomicity of every attaining measure beyond
(b)-(c).

**PA2** (headlines 2, 4; L). Closes `dsl:one-level-clusters`, `dsl:near-opt-mass`, `sr:single-level`, `dsl:hb-clusters`,
`dsl:hb-mass`. The cluster structure needs only the `O(1)` law; the exact first atom `d_1` and `(t_2^* - t_1^*) c^{-1/3}` need
`c_0^*` (FIVE-W; it uses `rig:R`, not `bl:norm`). The HB forms (`dsl:hb-clusters`: inactive extra sites by `ds:primal` (d);
`dsl:hb-mass`: raw masses on the fixed window and on shrinking windows `h_n = o(1)` by Markov on the moment bounds) need PM-3.
Needs PA1, W-P5, FIVE-W, PM-3 (HB forms).

**SR-COR, rest** (headline 2; S). Barycentre assertion (section 1.1); the single-level ratios `R_n` and `sr:eD1` belong to
`sr:single-level` (PA2; they need the Cardy density asymptotics, Lemma 4(f)).

**SE3, rest** (headline 2; S). Offset form of `se:3.3`.

**STAB, rest** (headlines 2, 4; S-M). `se:3.1` second assertion; concrete HB `se:terminal-stability`; its multilevel form.

**SLK, rest** (headlines 2, 4; S). `s`-variable form of `bl:norm`; HB1 for the identification at general `(P,Q)` (`hb_blnorm`
takes the node data for a given `D`). Optional in-place edits: re-derive `proposition_P_general`, `lemmaQ_general_part3` as the
`eta = 0` case of `densityHyp_of_slack`; make `continuousOn_deriv_virasoroDeltaChart`, `chartUT_mem_Icc_of_between`,
`cardyNorm_pos_of_nonzero_P` and the ArcBounds `deriv_airyAiC_ofReal` public (primed copies are in `SlackFeasible`).

**DU-F** (headlines 2, 4; S-M). `se:cdual`. Needs DU-G, PA1 (both in to the scope used at large charge).

**W-T2w, general `m`** (headline 4, HB level; L, 6-8k). `(f,r) = (m, m-1)`: `ut:ideal` (a), (b) at `m >= 3`, Remark T2.1,
`ut:Vac` for general `f >= 2`, `ut:IIF`, `ut:I`, `ut:III` for general finite real factors. No mathematical blocker. Not needed for
headlines 2, 3; needed for the HB taper `(m_0, m_0-1)` of `pmix:rigidity`(c) at `m_0 >= 3` (PM-3), since the design side at
`(w, Q = 1)` is open beyond `(2,1)` while the PM-2 transfer is design-independent. Steps: (1) `MZeroDesign m n` (real zeros
`p_1 > ... > p_m` with pair sites); (2) K7W, phase and inner comb for `r` Blaschke factors by induction (`mul_blaschkeT`,
`PhaseComb.mul_blaschkeT`); (3) Regions I/II for `f = m`, `gamma = m + 1/2`; (4) lobe (power `(x - xi_*)^{-(2f - 1/2 - r)}`),
band, far band and vacuum core with `F_{m,m-1} = FK^{(m)} (pi lambda/(2 sqrt 2))^{m-1}`; (5) port `IdealApprox*` (about 1.7k) to
`m` zeros ((b) then follows from Fatou and (a)).

**PM-1, rest** (headline 4; M). Signed-source lower half of `pmix:o1` (section 1.1); `pmix:liminf`; optional: `pmix:ramped`
uniform in `d in [0, d_0]` (rerun `rampedBumped_positive` with `d` variable; no downstream Lean consumer needs it), the separate
`|G| <= C (1+|u|)^{-5/2} e(u)` bound of `pmix:punif` (unused downstream).

**PM-2, rest** (headline 4; M). General `(f,r)` (design side first, then a copy of `VacTwoZeroWindow/Core/VacTwoZero`, about 700
lines); the two-sided second limit (at `(2,1)` within reach: `int_{|u|>R} |W_2| -> 0` and the window limit; `pmix:rigidity` uses
only `limsup_le`); the consumer ports (section 1.1).

**PM-4** (headline 4; S-M). `pmix:duality`: instances of `ds:M`, `ds:E`, `ds:primal`, `ds:LP` for mixtures. Needs PM-0, DU-G,
PA1, LP1 (all in to the scope used).

**FT-H4b** (headline 4; M-L). Realign `FTH4b` to the paper's H4b (`fold_tip_universality.tex`, `ft:hyp`, `\textlabel` `ft:H4b`):
general Hermite-Biehler data `(P,Q)`, terminal index `m`, support clause (a), one-sided designs (D1)-(D4); then Lemma WP
(`sr:window-pairing`), Lemma WR (`sr:WR`) and C5(c) at every HB level (`FTSigma` is the Airy level only). The present `windows`
field assumes tail bounds that are conclusions of WP, so it is replaced, not extended; re-point Concordance row C5c. Needs FT-1,
`Upper/Rigidity`.

**FT-CC** (headline 4; M). The base structure `ChartCompactness` (`compactness_subseq` plus site and tail positivity, abstract
setting, importing nothing Hankel- or Virasoro-specific). No open parent.

**PM-3** (headline 4; L). `pmix:hbphase`, `pmix:hbtap`, `pmix:rigidity`; `gt:2.1`, `gt:2.4`-`gt:2.6` for mixtures. Needs PM-1,
PM-2 (`pmix:vac` and the consumer ports), PM-4, PA2 (one-level part: `dsl:one-level-clusters`, `dsl:near-opt-mass`;
`pmix:rigidity`(c) cites `dsl:hb-clusters`, `dsl:hb-mass` only as forward pointers), W-T2w (`ut:ideal`; general `m` for the HB
taper), SLK, FT-H4b, W-P6.

**INT-2HB** (headline 4; L). `int:hb-reserve` (any strict HB pair; `m_0 = 1` is `int:reserve`), a sharp law with matching
upper bounds since PR 307 (`int:hb-res-sharp`: normalised infimum `(kappa_N^res + o(1)) n^{-1/3} eta`, maximal reserve
`R(B_n - eta; F_n) = (kappa_N^res/p_N + o(1)) n^{-1/3} eta`, uniformly for `0 < eta <= H(n)`, fixed source and HB pair). Needs
PM-3 (`pmix:rigidity`, `pmix:hbtap`), PM-2 (`pmix:vac`), W-T2w (`ut:ideal`), SLK, DU-F, PA1 (`ds:primal`), PA2
(`dsl:hb-clusters`), `pmix:o1`, `pmix:rebase`, `pmix:dominated` (PM-5 for the dominated clause).

**HB1** (headline 4; S-M after its inputs). `gt:hb` for general `(P,Q)` (the single-component case of `pmix:rigidity` with
`int:hb-reserve`, `sr:single-level`); closes `wone:ftlfw`, `wone:genlower` for all `m_0`. Needs PM-3, INT-2HB, PA2, FT-H4b, SLK,
PA1, LP1, FT-CC, Paper I M8 (TE.0' for all `(P,Q)`, via `ChartCompactness`).

**PM-5** (headline 4; S). `pmix:main` (assembly), `pmix:dominated` (Corollary PM-S, general `lambda`), `pmix:floor-criterion`
(PM-S0: uniform Cardy floor iff `lambda({0}) > 0` and `A(x) > 0`; cf. Lean `FloorData`). Needs PM-0 to PM-4, PA2 (`pmix:main`
(3)-(5)), INT-2HB, INT-3, INT-4, FIVE-W (`ctu:c0`), PM-0b.

**SPIN-F, rest** (headline 1; S-M). `spinnotes:S1` (a), (d), (e), `scal:C1`, `scal:C3` (stated as `Prop`s in `Spin/Statements`).
Modelling choices of the skeleton: holomorphy in two variables stated separately in each variable (no Hartogs in Mathlib); the
derivative-bound clause of S2.4 (1) and the `T`-invariance remark of S1 (a) omitted.

**SPIN-S4** (headline 1; L, 25k+). The fourteen `s4:*` labels. Needs SPIN-F rest, `rem:thmOloc`; done inputs SPIN-D (`sd:SD`),
`spinnotes:S21`-`S23`, `S22b`, `bl:T*`, `rem:thmL`, `lam:thmB`. Since PR 304 `s4:6.1` is restated (scope of the slack theorem).

**SPIN-Z** (headline 1; M analytic part, certificates later). `isl:main`, `isl:finite`, `spinnotes:K1`-`K4a`, `L0a`-`L9`.
Computer-assisted in the paper: exact-rational certificates for the real collar, the slit excesses and the first
intermediate-spin regime (K.4(2)); Arb enclosures for the small-spin edge excess (K.4(1)) and the remaining intermediate boxes
(K.4(3)); exact-rational plain bounds (K.4a).
- *Decision:* in Lean the enclosures are one named hypothesis structure `SpinZEnclosures`, one field per item, each stated
  exactly as the paper's check asserts it, with its box; SPIN-Z proves `isl:main`, `isl:finite` from it. Kernel-checked
  certificates wait until the other headline work is done (`decide +kernel` on exact rationals, or Mathlib's `dyadic_interval`;
  the `QVCheck` `native_decide` chain is not an acceptable precedent).
- *Fields (paper at `0932a6c6f`):* (1) the collar (`W = 0.037`, the `e_a` step); (2) the finite slit; (3) the slit tail; (4) the
  edge coefficients; (5) the edge saddle excess (`D_tot = D_s + D_e`, `D_s < 10.94`, `D_e < 3.73`, `D_tot < 14.67 < 20`), a bound
  on the nonnegative clamped excess `(E_eff - Delta Re h_4 + Delta r_*)_+`; (6a) K.4(2), `5e-5 <= Delta <= 0.0038`: one
  unregularised symbol `P_{4,0}` (explicit coefficient matrix of `p_2, p_3, p_4`) with the exact-rational bounds
  `(2/pi) int S/v^2 < 13.2 Delta^2`, `(2/pi) int (E + Delta r_*) < 8.4 Delta^2 + 0.00165 Delta`, weighted Wiener integral
  `< 70`, giving `12 C_1^eff <= -4.2 Delta^2 <= -1.05e-8` (`verify_spinning_integer_pf_unregularized.py`); (6b) K.4(3),
  `0.0038 <= Delta <= 0.072`: a finite contiguous box cover (twenty boxes in the Arb log, seven in the reduced-envelope route;
  the 37992-rectangle covering of the K.4 modulus is closed in `R556`); (7) the plain tip bound; plus the small-`Delta` symbol
  `P_4`. K.3 takes the clamped envelope `E~_0 = -Delta r_* + D_e Delta^2` with `E_quad < 1.5 Delta` and no `C_E` input (the
  former `C_E < 2` collar certificate is gone); K.2 covers only the unregularised multiplier `M_{K,0} = exp(a Delta P_{K,0})`
  (the `epsilon`-regularisation `eq:K19`-`eq:K21` was deleted), with tip vanishing of order 2 so inversion at `|q| = 3/2` costs
  `O(Delta |zeta|^2)`; L.4(b) and L.6(2) use `M = exp(a Q)` (the factor `a` was missing before PR 307) and `h = P_{4,0}(q_*)`;
  L.2(2)'s spin-zero floor is `rho_B(2s,0) * 2s >= (c_2/4) s e^{2 gamma a}` (factor `s`), absorbed by the `O(s)` numerators; the
  H.1 folded slit density is at most `2 v'(x)/(pi X)`. The historical six regularised K.4(2) boxes remain only as a TeX-internal
  alternative, not an input. Items (1)-(4) and K.4a need only
  elementary-function enclosures; the first target is the real-collar `P_4` bounds, which need a Ball enclosure layer (Mathlib has
  none: reuse `ThirdParty/interval`). A smaller `c_quad` may be possible (unverified, `R557`).
- *Lean-friendly discharge routes* (QIprojects PR 294; `notes/K4_LEAN_PATH.md`, exact-rational or interval certificates plus an
  analytic transfer proved there; `python-flint` not needed): (5) an exact-rational P4 edge (`verify_spinning_integer_p4_edge_
  {outer,tail,full}.py`; `D_e < 4.759`, `D_tot < 15.70`, `c1_{P4} > 43.10` against the paper's `3.73`, `14.67`, `44.13`; the
  weaker constants still close Part L); (6a) is now the paper's own route (above); (6b) a seven-box Check 5 cover in place of the twenty (`CERT_POLY_LEGACY=0`, worst
  margin `-1.776e-4`; Part L accepts the seven- or twenty-box cover), built on the global plain tip bound `f'' < -111` on
  `[0, 0.072]` (`verify_spinning_integer_plain_global.py`, item (7)); the single-anchor homotopies (`m1_homotopy`,
  `two_harmonic_homotopy`) are notes-level, not consumed by Part L. A field discharged by one of these routes is stated with that
  route's constants and says so; the paper's form stays the default.
- Needs SPIN-S4, SPIN-D (done).

**INT-T, rest** (headline 1; L, about 3.6k done of 8-12k). `int:cheb` at the paper's floor `640 N^2` (filtered inverse on the
oversampled grid: `Corr (2(M+1)) M R` for `R >= 320` by a de la Vallée-Poussin taper, `L^1` norms of the `K_j`, a contraction on
the `l^infty` cube; no obstruction known, 1.5-2.5k; check whether `int:main`'s prefactor depends on the floor exponent: if not,
`int:cheb` is off the headline path since `int:atom` takes an abstract floor); `int:sonine` (since PRs 299/301: compresses the
Hankel operator directly at real `w >= 1/2`; the small-band inverse bound `int:AB-bound` holds for every real `w >= 1`; Plancherel,
an `H^1` pointwise bound, Phragmén-Lindelöf in the slit plane, tensorisation `||P F^{(x)2w} P|| = ||P F P||^{2w}`, radial lift;
4-6k, no infrastructure); Weber's integral `int_0^oo e^{-2 pi beta t} 2 pi (t/s)^{(w-1)/2} J_{w-1}(4 pi sqrt(ts)) dt = beta^{-w}
e^{-2 pi s/beta}` (for `int:repair` (1); absent from the repo). INT-R uses the abstract projection repair (real `w >= 1`); INT-R0
needs pointwise crossing identities on the band.

**INT-1** (headline 1; M-L). `int:atom` (abstract floor `W(M)`, moment order `M_k >= K H_k / log P_k`). Inputs done (INT-T).

**INT-2** (headlines 1, 4; M-L). `int:reserve` (sharp joint large-charge law: normalised slope `(kappa_res + o(1))
c^{-1/3} eta`, maximal reserve `(2 kappa_res + o(1)) c^{-1/3} eta`, `kappa_res = 1/(2 ell_V L_*)`, uniformly for `0 < eta <= 1`;
variational formula `int:reserve-var`, i.e. `ds:E`(c)), `int:strict-weak`. Lower half: inputs in Lean for `(H_w)` and positive
mixtures, modulo the `bl:norm` check; upper half needs PA2 (section 1.1 step 5).

**INT-3** (headline 1; M). `int:main` and `int:hb-integer` (the HB-site version, with the same cluster-mass and concentration
clauses at every fixed terminal or later HB node). Needs INT-1, INT-2, INT-T, W-P6; PA2 (`dsl:one-level-clusters`, `dsl:hb-mass`,
`dsl:near-opt-mass`) for the cluster clauses; FIVE-W (`ctu:main`) for the five-term corollary; INT-2HB for `int:hb-integer`.

**INT-4** (headline 1; M). `int:obstr`(a): the supremal integer gap is attained; `Delta^Z = Delta^R` iff some attaining real
measure is integer-weighted (the "iff" needs PA1); (b), swap-invariant spin cones, is INT-S.

**INT-S** (headline 1; L). `int:axis-trace` (since PR 299 a weighted Hölder bound `||Phi||_1 <= 50 a^{-1/7} M_2[Phi]`, S2.4, no
axis-trace decomposition), `int:cheb2d`, `int:cheb2d-explicit`, `int:cos2d-repair`, `int:cont-spin` (any repair budget
`sum b_k <= 1/8`; lattice `b_k = 1/(8k(k+1))`; INT-7C drops `2 pi e R <= m`; continuous-spin moment orders `O((a+R^2)/log a)`;
uses `dsl:reserve` with weights `(1/2,1/2)` and the Virasoro product source, which is exactly the Lean `dslReserve`), and
`int:obstr`(b). Needs SPIN-S4 (`s4:S4`, `s4:eSlack`), SPIN-D (done), DU-G (done), INT-1 (`int:counting`), INT-4, INT-T, FIVE-U
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
- **W-T2w at `(2,1)`, SE3 at zero offset**: `twoSimpleZeroTransfer_all`, `theorem_two_five_all`, `theorem_two_six_all`,
  `wone_clark_two_level_boundary_all`, `se_crossing_corollary` (`TwoLevel/TwoZeroBump*`, `TwoZeroTransferW`, `WOneFiveClarkAll`,
  `SoftEdgeCrossingCorollary`). Optional cleanups: drop the unused `prob.w = 1` from `twoZeroF_eq_windowMeasureNormK`,
  `twoZero_band_bound`, `twoZero_window_comb` (and delete the `_w` variants); re-derive `twoZero_regionOne_a/b` from the `_lower`
  versions; generalise `twoZero_lobe_small/near/bound`, `twoZero_far_bound`; make the `_w1` forms thin wrappers of the `_all`
  versions.
- **DU-G**: `ds:E` (a), (b) compact `F`, (c), `ds:farkas` (`Duality/`). Route: finite-dimensional separation plus Carathéodory and
  a vague limit along an ultrafilter (`RealRMK.rieszMeasure`), no `[0,1]` compactification. Optional re-derivations:
  `TwoLevel.constrained_strong_duality` as clause 3 of `theorem_E_a`; `FixedWeight.theorem_E*` and Virasoro
  `Duality.theorem_E_b/_c` from `theorem_E_b_compact(_empty)`; `Upper.Rigidity.exists_vagueLimit` as the `Y = R` case of
  `exists_vagueLimitAlong`; `Duality/Farkas`, `Duality/MeasureCompactness` are subsumed. Optional corollary:
  `T_F^{[infty]} = T_V(c~;F)` for compact `F` (from `theorem_E_b_compact`, `ds_LP_i`, `ds_LP_b_imp_a`).
- **PA1, large charge**: `compact_negative_mass`, `T_V_pos_of_strip`, `fixedChargeStrip_of_large`, `theorem_primal`
  (`Duality/Primal/`).
- **LP1, LP1b**: `ds_cay_*`, `ds_cont`, `ds_mom` (with `lagP_oddFam_sharp`: `C_w = (2+w)/(2 pi)`), `poly_compact`,
  `positive_ray`, `ds_LP_i/ii/iii` (`LP/`, `Measure/PolyGrowthExtension`; design `LP/LP1_DESIGN.md`).
- **SPIN-F** (all but S1 (a),(d),(e), `scal:C1`, `scal:C3`): `spinS1b`, `spinS1c`, `spinS21`, `spinS22`, `spinS22b`, `spinS23`,
  `spinS24`, `spinS3` (`Spin/`).
- **SPIN-D** (`sd:R` partial since PR 307): `spinDM`, `spinDP`, `spinDSD`, `spinDW`, `spinDV`, `spinDA`, `spinDLP`, `spinDR`
  (the marginal Airy law; the `dsl:hb-mass` concentration clause of `sd:R` waits for PA2, then extend `SpinDR` in place), and
  `dslReserve` (`dsl:reserve`,
  `d = 2` swap-invariant form) (`Spin/SpinD*`). The exponential `L^1` bound `spinTestClass_exp_L1_le_M2` replaces the paper's use
  of `spinnotes:S24` in `sd:V`, `sd:A`. Lean's `a >= 2` is the paper's `c >= 25`.
- **SLK** (`u`-variable), **STAB** (`rem:thmBstab`; `se:3.1` first assertion; abstract `se:terminal-stability`), **SR-COR**
  (masses and positions): `Blowup/NormLimit*`, `Stability/`, `Upper/Rigidity/SpectrumCorollary`.
- **INT-T** (to its scope): `int_closed`, `cheb_explicit`, `ShellSetup.shell_inv`, `repair_identity_*`, `hankelDual_bound`
  (`Integrality/`).
- **PM-0, PM-1, PM-2** (to their scopes, all labels partial): `Mixtures/` (designs `PM0_DESIGN.md`, `PM1_DESIGN.md`,
  `PM2_DESIGN.md`).
- Earlier lanes: **A** (`O(1)` upper bound at `w = 1`, `Upper/Ramped/`), **B** (`Sigma_0`, `Sigma`), **C** (`N = 1`), **D**
  (bump at `w > 1`, P1-P4), **TL1-TL6** (two-level lane), **FT-0, FT-1, FT-2** (`FoldTip/`). Lessons kept: state the general lemma
  in its own file and re-derive the old declaration under its old name; state weight-one lemmas in an abstract-integrand form
  first (`rampedWindow_part_gen`). Open follow-ups of TL: the `integrable` field of `TwoZeroTransferData`; a shared core builder
  for `bootstrapHB_of_YVForWThr`/`_Clark` (about 200 duplicated lines).

### 2.3 Dependency edges and waves

Edges (a package waits for everything it needs; checked against the `\ref`s of each proof in the TeX, 2026-11-25/27):

```
FIVE-0 (done) -> FIVE-S (done) -> {FIVE-L, FIVE-U} -> FIVE-W <- W-P5, W-P6 (done), PM-0b        [headline 3]
DU-G (done) -> PA1 (large charge done) -> {INT-4, DU-F, PM-4} ; PA1 + W-P5 + FIVE-W -> PA2         [headline 2]
SPIN-F rest + rem:thmOloc -> SPIN-S4 -> {SPIN-Z, INT-S}                                              [headline 1]
INT-T -> INT-1 ; SLK + W-P6 + DU-G -> INT-2 lower ; + PA2 -> INT-2 upper ; INT-1 + INT-2 + PA2 (+ FIVE-W) -> INT-3  [headline 1]
PA2 (dsl:hb-mass) -> sd:R concentration clause                                                       [headline 1]
INT-1 + INT-4 + SPIN-S4 + FIVE-U -> INT-S                                                            [headline 1]
PM-1 + PM-2 + PM-4 + PA2 + W-T2w + SLK + FT-H4b -> PM-3                                              [headline 4]
PM-3 + SLK + DU-F + PA2 -> INT-2HB -> {HB1 (+ FT-CC, Paper I M8), PM-5 (+ INT-3, INT-4, FIVE-W)}       [headline 4]
```

| wave | open packages | why |
|---|---|---|
| 1 | FT-H4b, FT-CC, SPIN-F rest, SR-COR rest, SE3 rest, SLK rest, STAB rest, INT-T rest, PM-0b, W-T2w general `m`, PM-1 rest | no open parent |
| 2 | FIVE-L, FIVE-U, PA1 rest, INT-1, INT-2, INT-4, DU-F, PM-4, PM-2 rest | need wave 1 at most |
| 3 | FIVE-W, SPIN-S4 | |
| 4 | PA2, INT-3 (main part earlier), INT-S, SPIN-Z | SPIN-Z with `SpinZEnclosures` |
| 5 | PM-3 | |
| 6 | INT-2HB | needs PM-3 |
| 7 | HB1, PM-5 | |

A wave is an order, not a schedule. INT-2 and INT-4 are in wave 2 because their inputs are done; INT-3's main statement needs only
INT-1 and INT-2, its corollaries wait for FIVE-W and PA2.

### 2.4 Staffing and practice (owner decisions)

- No time boxes; a stalled route is a ledger row, not a stop. At most three runs at once; launch only with at least 1.5 GB disk free.
- Since 2026-11-26 (owner): no new Sonnet agents; agy `gemini-4-neon-medium` for the hardest L steps, agy
  `gemini-4-hydrogen-medium` for bounded steps, Haiku for docs and `THEOREM_MAP.md` rows. Agy drafts are checked against the
  paper before landing (as for every `from an agy draft, checked` commit).
- For each long lane (FIVE-*, SPIN-*, PM-*) five pushes adding results without moving the lane's headline force a direction
  statement.
- Shared files: the umbrella `FormalResearch/ModularBootstrap.lean` and `THEOREM_MAP.md` take targeted edits after merging
  `origin/master`; never apply an agent's stale umbrella as a diff.

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
| Primal attainment | `ds:primal`, `dsl:strip-fixed` | `theorem_primal`, `fixedChargeStrip_of_large` | `c~ >= c_0(w,Q)`; modulo `FixedChargeStrip` below |
| Theorem LP | `ds:LP`, `ds:cay`, `ds:cont`, `ds:mom`, `dsl:poly-compact`, `dsl:positive-ray` | `ds_LP_i`, `ds_LP_ii`, `ds_LP_iii`, `ds_cay_iff`, `ds_cont`, `ds_mom`, `poly_compact`, `positive_ray` | `(H_w)` |
| Clark curve, `se:3.2` | `gt:2.1`, `wone:genlower`(2), `se:3.2` | `concrete_two_level_theorem`, `theorem_W1prime_two`, `A2star_lipschitzOn` | every `(w,Q)` |
| Corollary 2.4, Theorems 2.5, 2.6, T2, Clark boundary, `se:3.3` | `gt:2.4`-`gt:2.6`, `ut:T2`, `wone:clark`(c), `se:3.3` | `corollary_two_four_all`, `theorem_two_five_all`, `theorem_two_six_all`, `twoSimpleZeroTransfer_all`, `wone_clark_two_level_boundary_all`, `se_crossing_corollary` | every weight; two-zero designs `(2,1)`; `se:3.3` zero offset |
| Normalisation limit, stability, clusters | `bl:norm`, `rem:thmBstab`, `se:3.1`, `se:terminal-stability`, `sr:cor` | `airy_blnorm`, `clark_blnorm`, `hb_blnorm`, `airy_stability`, `clark_stability`, `terminal_stability`, `cluster_mass_tendsto`, `cluster_position_tendsto`, `crossing_cluster_mass` | see section 7 rows |
| Fold-tip instances (Paper I's FT) | `ft:FT` | `ft_fixedWeight_all`, `fw_foldTip_hypotheses_all`, `ft_virasoro`, `ft_n1` | C1-C4, C5a-C5c (Airy level) at every `(w,Q)` |
| Five-term constants | `cts:langer`, `cts:phaselock`, `cts:main`, `pm:tip-match`, `cts:tip-shared` | `comb_minimum_virasoro_c0Star`, `g3Out_eq_g3Vir`, `gamma0_eq_gamma0Of_out`, `tip_match`, `airyLinearMoment`, `airyBC_id` | Virasoro |
| Five-term halves (conditional) | `thm:spinless-expansion` | `spinless_upper_of_inputs`, `spinless_lower_of_inputs` | Virasoro, modulo `UpperMainInputs`, `LowerMainInputs` |
| Continuous spin | `spinnotes:S3`, `sd:*` | `spinS3`, `spinDSD`, `spinDA`, `spinDR`, `spinDLP` | `a >= 2` (`c >= 25`) |
| Mixtures, integrality tools | `pmix:*`, `int:*` | `MixtureData.pmix_o1_mixture`, `pmix_vac_f1`, `twoSimpleZeroTransfer_src`, `int_closed`, `cheb_explicit` | see section 7 rows |

## 5. Scope caveats, hypotheses and paper findings

### 5.1 Scope caveats (so nobody cites a Lean statement as the paper's)

- `FixedWeightProblem` is integer `w` with a product `Q`; "every `(w,Q)`" means that class. Real `w`, mixtures and unflavoured
  `N = (2,2)` are outside it.
- `ds:E`: (b) carries the extra hypothesis `0 < T_V` (discharged by `T_V_pos_of_strip` or the lower bounds); statements over
  `DualSetupCore`; every "has a subsequence" step is along an ultrafilter `<= atTop`; the Laplace-integrability hypothesis of (c)
  is not needed (it follows from `h in L^1(sigma)` via `w_* <= h`). Since PR 299 the paper's `ds:E` attains the reserve at the
  endpoint even with zero residual budget: check `theorem_E_c_reserve` covers that case. `corollary_E1` and `ds:E1` give a
  crossing measure with gap exactly `T_V`; atomicity comes only from `theorem_primal`.
- `ds:primal`: proved for `c~ >= c_0(w,Q)`; for `12 S <= c~ < c_0` it takes `FixedChargeStrip prob c~`; the paper claims
  `dsl:strip-fixed`(a) for every `c~ >= 12 S`. The clause "real-analytic on `(-a,inf)`" is replaced by what the proof uses
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
- Named input structures that are still hypotheses somewhere: `FixedChargeStrip` (below `c_0`), `FTH4b` (also the wrong form,
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

### 5.3 Lean targets changed by QIprojects PR 307 (merged `0932a6c6f`)

Already applied in the rows above; listed so existing Lean statements are checked against them.
- `int:reserve`, `int:hb-reserve`: lower bounds became a sharp joint large-charge law with matching upper bounds
  (`int:hb-res-sharp`); the variational formula `int:reserve-var` now precedes INT-2. No Lean yet; plan rows INT-2, INT-2HB.
- `int:main`, `int:hb-integer`: cluster-mass equivalents and exponential concentration via `dsl:hb-mass` (PA2). Row INT-3.
- `sd:R`: concentration bounds via `dsl:hb-mass`; `spinDR` now covers part of it (`sd:R` done -> partial). The SD3 derivation
  (log-temperature reflection) is outside any result environment.
- `ctu` transfer table (FIVE-W proof route only): C10 descendant log constant and the Region-I `Q`-ratio. Row FIVE-W.
- SPIN-Z: K.2 (unregularised multiplier only; `eq:K19`-`eq:K21` and `verify_spinning_integer_CE_bound.py` deleted), K.3 (no
  `C_E`), K.4(1)-(2), L.2(2), L.4(b), L.6(2), H.1. Row SPIN-Z. CORRECTIONS rows in `CFT/modular_bootstrap/notes/CORRECTIONS.md`.

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
  the base structure `ChartCompactness` is owned by this lane (FT-CC); Paper I adds, without editing `RadialRigidity.lean`, a
  converter `RadialRigidityPackage -> ChartCompactness`, and its M8 TE.0' is a converter into `ChartCompactness` plus the shared
  rigidity theorem. Steps 3-4 start when `ChartCompactness` is on master: it is not (Paper I's `HbMultilevelInputs.lower` docstring
  refers to it, no declaration exists). Paper I's `lem:qual-compact` is in Lean (`Analysis/QualCompact`: `qual_compact`,
  `qual_compact_real`); Paper II's `compact_negative_mass` is not re-derived from it (it assumes pointwise convergence off one
  compact set, not local `L^1` convergence); use `qual_compact` for `bl:norm`-type or FT-3..6 needs.
- Paper I does not plan Lemma WP, Lemma WR or `teb:quant_c1_near`; here they are FT-H4b and FIVE-L.
- **Five-term lower bound: shared analytic cores** (`SignUncertainty/PLAN.md` section 5, item 7). FIVE-L (`ctl:dyadic`,
  `ctl:pass2`, `cts:rosc-uncond`, `cts:boas`) and Paper I's F1 (`ct:dyadic`, `ct:boas`) are one mechanism for two phases;
  phase-free cores have one copy. Here: `LowerBoasResidue` (`boas_residue_zero`, `rect_boundary_zero`), `LowerDyadic`
  (`markov_select`, `dyadic_term_le`). Paper I: `CtHalfDiscPoisson`, `CtFejer`, `CtSd*` (`sd_eval`), `CtCfu*`, `CtMorse*`, and the
  shared `Complex/HalfDiscCauchy` (`halfDisc_cauchy`), `Complex/HalfDiscPoisson` (`halfDisc_poisson`, upper half-disc; this lane's
  `FiveTerm/HalfDisc*` is the right half-disc, a different object), `Asymptotics/DyadicAbsorption` (`absorb_dyadic`). Owned by
  F1 and listed open there: the scale-`r` strip-band reduction and the scale-`r` bootstrap family with good-circle selection,
  stated phase-free where possible, which FIVE-L's `ctl:dyadic`/`ctl:pass2` instantiate. Since that agreement F1 has proved much of
  its stack (`ct_boas_concrete`; `ct_lower` modulo `CtLowerInputs.dyadic`; `CtBandData`, `CtEtaTransfer`, `CtRoscBook`): FIVE-L
  starts with the reuse audit of section 1.1 and `git grep`s `Complex/`, `Asymptotics/`, `TwoEdgeBootstrap/`, `SignUncertainty/`;
  any new shared core goes to whichever lane needs it first, which records it in both plans.
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
  `wone:ftlfw` at `m_0 = 1` (Airy) and `m_0 = 2` (Clark pair); general `(P,Q)` and real `w`: HB1; `wone:genlower` parts (1),
  (2).

### 7.2 Blow-up, rigidity, weight axioms
- **BL** (`bl:T`, `bl:T1`, `bl:T2`, `bl:T4`, `bl:T5` done; `bl:norm` partial): tests with `g_vac >= 0`; `bl:norm` in the Langer
  `u`-variable with prescribed-node data as hypotheses (SLK rest). Lemma T3 is `lemma_T3_unconditional`.
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
  `SigmaConclusion` (discharged by `sigma_unconditional_probW`), no barycentre.
- **UP** (no paper label; `pmix:ramped` at one component): done at every weight.

### 7.4 Two-level curve and soft-edge stability
- **TL** (`gt:2.1`, `se:3.2` done; `gt:2.4` (aliases `gt:2.5`, `gt:2.6`), `gt:hb`, `se:3.3`, `se:cdual`,
  `se:terminal-stability`, `se:3.1` partial): `gt:2.4` partial only for mixtures (PM-3); `gt:hb` at `m_0 = 1, 2` (HB1);
  `se:cdual` only `F = {t_1}` (`constrained_strong_duality_two_level`; DU-F); `se:3.3` zero offset; `se:3.1` first assertion;
  `se:terminal-stability` abstract, terminal-node case (the paper's is multilevel since PR 304). `theorem_SE7`,
  `theorem_SE7_uniform` are the Virasoro `O(log c')` forms.
- **STAB** (`rem:thmL`, `rem:thmBstab` done; `rem:corL` partial; `rem:thmOloc` planned): `rem:thmBstab` for any entire `L^1`
  `AiryG` of the stated growth, non-vanishing as `exists x, f x != 0`; `rem:corL` = `corL_virasoro` (FIVE-L).

### 7.5 Duality, attainment, infinite-order limit
- **DU** (`ds:D1`, `ds:M`, `ds:E` done; `ds:farkas`, `ds:E1` partial): `ds:farkas` without the symmetry clause, second
  countability in place of the paper's metrizable one-point compactification; `ds:E1` atomicity not combined with
  `theorem_primal` into one statement.
- **PA** (`ds:primal`, `dsl:strip-fixed` partial; `dsl:one-level-clusters`, `dsl:near-opt-mass`, `dsl:hb-clusters`,
  `dsl:hb-mass` planned; `dsl:compact-mass` recalled): section 5.1.
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
- **FIVEL** (`cts:edge-hankel`, `cts:lower-main`, `cts:rosc-uncond` partial; `cts:boas`, `cts:cauchy-dual`, `ctl:*` planned):
  section 2.1.
- **FIVEU** (`pm:tip-match`, `cts:tip-shared` done; `cts:smooth-env`, `cts:transfer` partial; C11-C14 planned): section 2.1.
- **FIVEW** (`ctu:O1`, `thm:spinless-expansion` partial; `ctu:main`, `ctu:table`, `ctu:weight`, `ctu:strip`, `ctu:tip-window`,
  `ctu:tip-kernel`, `thm:fixed-weight-expansion` planned).

### 7.7 Positive mixtures
- **PM** (nine labels partial, seven planned). Scopes: `pmix:rebase` (local finiteness of weighted push-forwards a hypothesis;
  `nu_j` on `(0,oo)`, `W_j >= 0` measurable, `n_j > 12 r`; since PR 301 an exact affine push-forward identity); `pmix:weight`
  (atomic `lambda`; the nonnegative-Taylor-coefficient clause of (a) not formalised); `pmix:crossing` ((b) in the abstract form of
  `fwM_of_decay` with `|h_0(-alpha)| <= 2` a hypothesis; the `AdmissibleSpectrum` corollary not ported); `pmix:jets` (only
  `pmix_jets_hyp` and `MixtureData.pmix_jensen`, whose integrability is a hypothesis; since PR 301 the paper's form is an exact
  integrated relative-entropy identity); `pmix:punif` (no separate `-5/2` bound on `G`); `pmix:ramped` (at
  `d = M0 c'^{-1/3}` for each fixed `M0`); `pmix:smooth` (coefficient `1/2` for `3/8`, hypothesis (i) on the whole window, vacuum
  step at `d = M0 c'^{-1/3}`); `pmix:o1` (lower half for positive mixtures only; `pmix:liminf` not covered; since PR 304 a
  strictness clause, not in Lean); `pmix:vac` (`(1,0)`, `(2,1)`, any common source; second limit one-sided; `g > 0` proved where
  the interface asks `0 <= g`; Lean absorbs the paper's `sqrt(n') lambda^gamma = o(1)` transform step into the window comparison;
  at `f = 1` the lobe is controlled by sign, not the paper's absolute tail bound). Optional: generalise W-P5 in place to sources
  (`VacWindow/VacCore/VacProp` become wrappers); re-derive `Crossing/SumRule` from the ported forms (needs
  `crossingBounds_ofProblem`); general Borel `lambda`.

### 7.8 Integrality
- **INT** (`int:int-closed`, `int:shell-inv`, `int:cheb-explicit`, `int:repair-identity` done; `int:repair` partial; `int:cheb`,
  `int:sonine`, `int:atom`, `int:reserve`, `int:strict-weak`, `int:hb-reserve`, `int:main`, `int:obstr`, `int:hb-integer`
  planned). `int:int-closed` for proper metric spaces (the paper's closed `Y ⊆ R^d` is a special case); `int:shell-inv` with the
  cell step a hypothesis (as in the paper's use), Lean stage `j` = paper `k-1`, `nu_Z` a `Measure.sum` (merging coincident atoms
  not formalised); `int:repair-identity` with the existence of `f` from `||P U P|| < 1` a hypothesis; `int:repair`: the Taylor core
  `hankelDual_bound` (`int:Hw-eta` in the `1/m!` form) and part (2).
- **INTL** (5 not planned). **INTS** (5 planned).

### 7.9 Spin
- **SPINF** (`spinnotes:S21`, `S22`, `S22b`, `S23`, `S24`, `S3` done; `spinnotes:S1` partial; `scal:C1`, `scal:C3` planned).
- **SPIND** (seven `sd:*` done; `sd:R` partial: the concentration clause via `dsl:hb-mass`).
- **SPIN4** (fourteen `s4:*` planned). **SPINZ** (eighteen labels planned; enclosures as `SpinZEnclosures`).

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

Every stated result of the paper and supplement at `0932a6c6f`, by file. Format: state / group: labels (aliases). D done, P partial,
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
- P / FIVEL: `cts:edge-hankel`, `cts:lower-main`, `cts:rosc-uncond`
- PL / FIVEL: `cts:boas`, `cts:cauchy-dual`
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
- PL / PA: `dsl:one-level-clusters`, `dsl:hb-clusters`, `dsl:hb-mass`, `dsl:near-opt-mass`

**`edge_transform_sd.tex`** (6)
- D / ESD: `esd:asym`, `esd:hankel`, `esd:global`, `esd:phase`, `esd:lemmap`, `esd:lemma`

**`integrality.tex`** (14)
- D / INT: `int:int-closed`, `int:shell-inv`, `int:cheb-explicit`, `int:repair-identity`
- P / INT: `int:repair`
- PL / INT: `int:sonine`, `int:cheb`, `int:atom`, `int:reserve`, `int:hb-reserve`, `int:strict-weak`, `int:main`, `int:obstr`,
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
  `pmix:vac`
- PL / PM: `pmix:main`, `pmix:dominated`, `pmix:floor-criterion`, `pmix:duality`, `pmix:hbphase`, `pmix:hbtap`, `pmix:rigidity`

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
- D / TL: `se:3.2`
- P / TL: `se:cdual`, `se:3.3`, `se:terminal-stability`, `se:3.1`

**`spectral_rigidity.tex`** (5)
- P / SR: `sr:P`, `sr:Sigma0`, `sr:Sigma`, `sr:cor`
- PL / SR: `sr:single-level`

**`spinning_calibration.tex`** (2)
- PL / SPINF: `scal:C1`, `scal:C3`

**`spinning_dual.tex`** (8)
- D / SPIND: `sd:M`, `sd:P`, `sd:SD`, `sd:W`, `sd:V`, `sd:A`, `sd:LP`
- P / SPIND: `sd:R`

**`spinning_foundations.tex`** (7)
- D / SPINF: `spinnotes:S21`, `spinnotes:S22`, `spinnotes:S22b`, `spinnotes:S23`, `spinnotes:S24`, `spinnotes:S3`
- P / SPINF: `spinnotes:S1` ((b), (c) proved; (a), (d), (e) stated as `Prop`s)

**`spinning_integer_exact_slope.tex`** (5)
- PL / SPINZ: `spinnotes:K1`, `spinnotes:K2`, `spinnotes:K3`, `spinnotes:K4`, `spinnotes:K4a`

**`spinning_integer_liouville.tex`** (11)
- PL / SPINZ: `spinnotes:L0a`, `spinnotes:L0b`, `spinnotes:L1`, `spinnotes:L2`, `spinnotes:L3`, `spinnotes:L4`, `spinnotes:L5`,
  `spinnotes:L6`, `spinnotes:L7`, `spinnotes:L8`, `spinnotes:L9`

**`spinning_integer_overview.tex`** (2)
- PL / SPINZ: `isl:main`, `isl:finite`

**`spinning_s4.tex`** (14)
- PL / SPIN4: `s4:S4`, `s4:2.1`, `s4:2.2`, `s4:2.3`, `s4:2.4`, `s4:3.3`, `s4:3.4`, `s4:4.1`, `s4:4.2`, `s4:4.3`, `s4:5.1`, `s4:5.2`,
  `s4:6.1`, `s4:4.4`

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

Files with no stated result: `modular_bootstrap_main.tex`, `five_term_roadmap.tex`, `spinning_integer_poincare.tex`,
`spinning_integer_multipliers.tex`. Totals: 262 results; done 104, partial 49, planned 80, not planned 6, recalled 23.

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
