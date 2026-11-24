# Paper II (modular bootstrap at large c) — Lean plan

Source: QIprojects `CFT/modular_bootstrap/paper/` (`airy_scale_core.tex` and its appendices, the technical supplement)
and the notes `CFT/notes/n2_ramped_comb.tex` (Lemma U*, `rem:thmU`). Audit 2026-11-23 (after A–C), reasoner `9a465bf`,
QIprojects `origin/main`. The paper status line for readers is the Paper II section of QIprojects `docs/lean_status.md`.

## 1. Proved on master (unconditional, pinned axioms `[propext, Classical.choice, Quot.sound]`)

| result | TeX | Lean headline |
|---|---|---|
| Lower bound `T_V ≥ T_* − C` at every integer `(w,Q)` in `(H_w)` (W1'(1), Theorem J) | `lower_o1_two_edge.tex` | `FixedWeightBand.fixedWeightLowerBoundInput_of_problem` |
| Virasoro two-term law `Δ_best = c/Λ_V + A_opt c^{1/3} + o(c^{1/3})` | `dual_spectrum.tex` E1, FW-C | `Upper.Assembly.virasoro_corollary_E1_littleO_unconditional` |
| **O(1) two-sided law at Virasoro** `Δ_best = c/Λ_V + A_opt c^{1/3} + O(1)` (O(1) upper half of C15 via Lemma U*) | `n2_ramped_comb.tex` `rem:thmU`, `ds:E1` | `Upper.Ramped.theoremC15UpperInput_virasoro`, `virasoro_corollary_E1_unconditional` |
| Property (P) for the `f = 1` designs `D(N,η_*,d)`, `η_* > 0` (Lemmas W, ID, A_V, T, R; Props I, II, V; K7) | `upper_transfer.tex`, `spectral_rigidity.tex` `sr:P` | `designPropertyP_virasoro` |
| Σ₀ and Σ at Virasoro for the extremal measures | `spectral_rigidity.tex` `sr:Sigma0`, `sr:Sigma` | `Upper.Assembly.virasoro_sigmaZero_unconditional`, `virasoro_sigma_unconditional` |
| O(1) upper bound and two-sided law for every `w = 1` problem; N = 1 corollaries | `n2_ramped_comb.tex`, `n1_super_virasoro.tex` | `Ramped.theoremC15UpperInput_prob`, `Assembly.n1_corollary_E1_unconditional`, `n1_sigma_unconditional` |

Σ₀, Σ also for every `w = 1` problem (`sigma_unconditional_prob`).

## 2. Done packages (record)

- **A. O(1) upper bound at w = 1** (route U*, `Upper/Ramped/`, R1–R8; `theoremC15UpperInput_virasoro`). Lessons kept:
  generalise in place (state the general lemma in our own file, re-derive the old declaration with the same name);
  finite rational hole product (no Euler products); statements uniform in `d` and `C_I, C_mid`.
- **B. Σ₀, Σ** (`Upper/Rigidity`, `Upper/Assembly`): Property (P) for any bounded offsets; the omitted family uses
  `f = 1` far-first-site designs (`farFamily`); the TeX keeps its `f ≥ 2` Step 6 with an internal note (owner decision).
- **C. N = 1** (`FixedWeightBand.n1_lowerBoundInput`, `Upper/Assembly/N1.lean`).
- Already in Lean before this plan, not to be redone: Prop T, Theorems C, R1–R3 at every integer `(w,Q)`
  (`FixedWeightTip/BlowupAndRigidity`, `Blowup/PropositionT`, `Rigidity/AiryRigidity`); strong duality D1, Lemma M,
  F_sep, Theorem E (`Duality/`, `FixedWeight/StrongDuality`); FW-A/X/C (`Crossing/`); Clark two-node theorem gt:1.2
  and the Clark quadrature (Paper I: `SignUncertainty/ClarkTwoNode`, `Special/AiryClark*`).

## 3. Targets (audit 2026-11-23, after A–C)

**TL. Two-level Clark curve** (`virasoro_two_level.tex`; new directory `TwoLevel/`).

| pkg | content | size | depends | state |
|---|---|---|---|---|
| TL1 | `A2star` (definition via `clarkNode α 2`, monotone, range, endpoints) and Theorem 2.1 `gt:2.1` (liminf ≥ A₂*, equality case → c·g_α) at every integer (w,Q) | M | Prop T, gt:1.2 | done (`TwoLevel/`, `concrete_two_level_theorem`, `_equality`); in-place re-derivation of `AiryRigidity` helpers pending (patch `/home/user/scratch/mb/tl1_inplace/`) |
| TL2 | Prop 2.3 `gt:2.3` qualitative: `u₂*(K) < z₂`, `→ z₂` (rate skipped) | S–M | gt:1.2, `airyNC_quadrature` | done (`TwoLevel/WindowOptimum*`; decay `K^{-1/15}` only) |
| TL3 | Constrained strong duality on `{t₁} ∪ [τ,∞)` (generalise `theorem_E` in place), Cor 2.4 `gt:2.4` | M | TL1, Theorem E, C15 upper (w = 1) | done (`TwoLevel/ConstrainedDuality`, `CorollaryTwoFour`); in-place patch pending (`/home/user/scratch/mb/tl3_inplace/`) |
| TL4 | Thm 2.5 `gt:2.5` and Thm 2.6 `gt:2.6` from a named `TwoSimpleZeroTransfer` Prop (T2, with non-vacuity) | M–L | TL1, TL2, FW-X, Property (P), `Upper/Rigidity` | 2.5 done given T2 and `TwoZeroNegativeVacuum` (`TwoLevel/Exclusion`); TL4b: prove `TwoZeroNegativeVacuum` (Airy f = 2 window algebra) and the node-level Clark rigidity for 2.6 (draft `theorem_two_six` held in `/home/user/scratch/mb/tl4_hold/`: its `ClarkRigidityFromDesigns` hypothesis is too close to the conclusion to merge) |
| TL5 | Theorem T2 `ut:T2` at w = 1 (f = 2 reference comb, tanh factor T_{χ(p)}, Regions I/II, window limit, vacuum with a positive deep lobe). Scout: K0–K8, A_II, Lemmas P, Φ, W, ID, R, T, Prop II, K7 are already f-general; f = 1 wiring only in `Positivity/RegionOne*`, `Vacuum*`, `Assembly/Psi*`. WP1 dictionary [M], WP2 comb + T-factor + K7 [M], WP3 Region II [S–M], WP4 Region I [M], WP5 window [M], WP6 vacuum limsup [L, critical], WP7 assembly and restate the T2 Prop for `prob.w = 1` with integrability [S–M] | L (4.5–6.5k) | — | WP1 running |
| TL6 | Two-level lower bound W1′(2) (`wone:ftlfw`, m₀ = 2): TE.0′ at α ≠ 0, Lemma Q and arc bounds at ψ_α, two-node `P_theta_bound`; then `se:3.2` | L (3–5k) | `BootstrapHBInstance`; TE.0′ overlaps Paper I M8 (coordinate) | later |

**FT. Fold-tip theorem** (Appendix D: `fold_tip_universality.tex` FT, `fold_tip_two_edge.tex` FT-2E; new directory
`FoldTip/`). For Paper II's own instances (Virasoro, N = 1, fixed (w,Q)) the conclusions C1, C2, C3 (O(1) form), C5a,
C5b, and C5c at w = 1 are already proved by other routes; FT reuses those proofs (no refactor of Prop T / Theorem R /
Σ through FT: ~8k lines at stake for little gain).

| pkg | content | size | depends | state |
|---|---|---|---|---|
| FT-0 | Concordance: one bundle theorem per instance (fixed weight: C1, C2, C3-O(1), C5a, C5b, C4/C2-full with H3 = `TheoremC15UpperInput` as hypothesis, C5c at w = 1; N = 1 unconditional) | S | none | done (`FoldTip/Concordance`) |
| FT-1 | `FoldTipScale`, hypothesis structures H1, H2 (H2hol), H2+, H3, H4a, H4b; `ofFixedWeight` from `proposition_P_of_problem`; chart bridge `Upper/Rigidity/Dictionary` | M | FT-0 | done (`FoldTip/Hypotheses`, `FoldTip/Instances`: all hypotheses for every `w = 1` problem; H3, H4b open for `w > 1`) |
| FT-2 | FT-2E and FT-Sub over `teb_bootstrap_part3/_hb`, `teb_mellin_o1_lower`, `WeakFeedback` (import only) | S–M | none | done (`FoldTip/TwoEdge*`); instance: expose the violator family and chart coverage from `theoremFTLFW_W_of_YVFor` Case 2 (`BootstrapWMain`, `ConcreteBootstrap/BootstrapHB`) and re-derive in place: FT-2b done (`FoldTip/TwoEdgeInstance`, `ft_fixedWeight_twoEdge`); re-derivation patch `/home/user/scratch/mb/ft2b_inplace/` pending |
| FT-3..6 | Abstract chart-form compactness (Lemmas 1–2) for arbitrary instances, C5d m ≥ 2, Lemma FT-R log rate | L | only useful for Paper I instances; a shared package with Paper I's `RadialRigidityPackage` is a cross-session decision | deferred |
| FT-7 | Modular Clark/HB FT-2E (m₀ = 2) | L | = TL6 | with TL6 |

**D. Later, not scheduled:** designs and bump at w > 1 (W1.4, Prop III, FW-M; makes H3/C15 and Σ unconditional for
w > 1), soft-edge slope `se:3.1`, continuous spin (`spinning_dual.tex`, nothing in Lean), real w and N = (2,2)
(weights outside (H_w)). **Out of scope:** five-term expansions C15/ctu.5, integer spin (computer-assisted), numerical
constants (0.4837…, 0.2070…, 1.2180…).

**Schedule.** Sonnet high for TL1, TL3–TL6; Sonnet medium for TL2, FT-1, FT-2; Haiku for FT-0, docs and THEOREM_MAP.
At most two Sonnet-high agents at once. Launch while ≥ ~1.5 GB disk is free.

## 4. Boundary with the Paper I session (checked 2026-11-23)
- Paper I owns `SignUncertainty/`, `CohnElkies/`, `TwoEdgeBootstrap/`, `Special/Airy*`, `Complex/`, `Analysis*`,
  `Asymptotics/` (plan: `FormalResearch/SignUncertainty/PLAN.md`). No `su/*` branch touches `ModularBootstrap/`.
  Paper II imports `TwoEdgeBootstrap` (`teb_bootstrap_part1`) and `Special` but does not edit them.
- Their M5 plans to "refactor the Virasoro `ArcBounds`/`QuadratureBounds`" for the Hankel TE.3 instance. Our
  `FixedWeightBand/BootstrapW*` already generalises those instances to every weight `w`; the Hankel instance should
  start from that pattern. Paper II does not refactor `ConcreteBootstrap/` or `TwoEdgeBootstrap/`.
- Langer charts are separate objects (Paper I: Hankel/Bessel density, `gt:7.7b/c/p`; Paper II: the Virasoro comb
  density, `Ramped/LangerTau*`). Mellin strips likewise (`SignUncertainty/MellinStrip*` for the Hankel kernel,
  `FixedWeightBand/Mellin*W` for the weight-`w` Bessel weight). No duplication.
- Fold-tip FT moved from Paper I to Paper II (QIprojects `45564ae42`); Paper II formalises FT-0..FT-2 in `FoldTip/`
  (imports `TwoEdgeBootstrap`, edits nothing there). `FoldTipSeed.lean` serves only Lemma L (H3 from a lift) and is
  not used. TE.0′ beyond α = 0 (TL6/FT-7) is Paper I's M8: coordinate before starting.
- Shared files: the umbrella `FormalResearch/ModularBootstrap.lean` and `THEOREM_MAP.md` (targeted edits after
  merging `origin/master`; never apply an agent's stale umbrella as a diff).
