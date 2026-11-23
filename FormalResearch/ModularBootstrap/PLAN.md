# Paper II (modular bootstrap at large c) — Lean plan

Source: QIprojects `CFT/modular_bootstrap/paper/` (`airy_scale_core.tex` and its appendices, the technical supplement)
and the notes `CFT/notes/n2_ramped_comb.tex` (Lemma U*, `rem:thmU`). Audit 2026-11-23, reasoner `24b2022`,
QIprojects `origin/main`. The paper status line for readers is the Paper II section of QIprojects `docs/lean_status.md`.
Earlier detailed plans (`U6_PLAN.md`, `UPPER_PLAN.md` in the working session's scratch) are superseded by this file
except for the step-level reuse tables of U6, recalled where needed below.

## 1. Proved on master (unconditional, pinned axioms `[propext, Classical.choice, Quot.sound]`)

| result | TeX | Lean headline |
|---|---|---|
| Lower bound `T_V ≥ T_* − C` at every integer `(w,Q)` in `(H_w)` (W1'(1), Theorem J) | `lower_o1_two_edge.tex` | `FixedWeightBand.fixedWeightLowerBoundInput_of_problem` |
| Virasoro two-term law `Δ_best = c/Λ_V + A_opt c^{1/3} + o(c^{1/3})` | `dual_spectrum.tex` E1, FW-C | `Upper.Assembly.virasoro_corollary_E1_littleO_unconditional` |
| Property (P) for the `f = 1` designs `D(N,η_*,d)`, `η_* > 0` (Lemmas W, ID, A_V, T, R; Props I, II, V; K7) | `upper_transfer.tex`, `spectral_rigidity.tex` `sr:P` | `designPropertyP_virasoro` |
| Σ₀ at Virasoro for the extremal measures | `spectral_rigidity.tex` `sr:Sigma0` | `Upper.Assembly.virasoro_sigmaZero_unconditional` |
| O(1)-upper inputs so far: Lemma P_unif (R1), Langer coordinate Prop 1.2(1), (F1), (F2) (R2a) | `n2_ramped_comb.tex`, `remainder.tex` | `Ramped.lemma_P_unif`, `Ramped.langerTau_spec`, `langerChart_F1/F2`, `langerTauInv_expansion`, `siteGap_two_sided` |

Conditional: Σ (`virasoro_sigma`) needs `DisplacedFamily` and `OmittedFamily` for a design class with Property (P).

## 2. Targets, in order

**A. O(1) upper bound at Virasoro: `TheoremC15UpperInput virasoroProblem`** (route U*, w = 1 only, no bump, FW-U
retired; the docstring cites `rem:thmU` of `n2_ramped_comb.tex`). With the lower bound this gives
`Δ_best = c/Λ_V + A_opt c^{1/3} + O(1)` two-sided. Packages under `Upper/Ramped/` (statement chain S0–S10 of
U6_PLAN §1, unchanged; TeX re-checked against `origin/main`):

| pkg | content | state / depends |
|---|---|---|
| R1 | P_unif, profile Lemma V/E/G | done |
| R2a | Langer chart τ, τ⁻¹, (F1), (F2) | done |
| R3a | Phase machinery uniform in N: squared pair-change bound (PC) `‖∂^iΔ_D‖ ≤ K Σ(|ε_j²−ε0_j²| + 2|χ'_j−χ_j|)`, N-free `combTail_K1a`, SDV hypotheses / Lemma Φ transform / global bound / K7 for an abstract design with c'-independent constants | done (`Ramped/PhaseUniform`, in-place generalisation of `Design/*`, `Membership/DesignMembership`) |
| R4 | Hole comparison: Λ-form of K4 for an arbitrary comb, comparison `log|B_D| ≥ log|B_ref| − S + Σ_H log ρ_k`, `R(t)` discriminant lemma, seven-pair product, near-tip ratio `vρ_∞ ≤ C_v r^{5/4}` | done except the named `ShiftSumEstimate` (Lemma-E summation; discharge in R3b) |
| R2b | Prop 1.2(2) comb-to-Airy identity, uniform over designs, error `O(c'^{-2/3})` | done (`Ramped/CombToAiry*`, for `combBD`; bridge to the ramped `designComb` in R5/R7) |
| R3b | Ramped instantiation (sites, heights, PC sums, SDV, Φ transform θ=3/5, K7, far-band comparison) | R3a, R4 done; also discharges `ShiftSumEstimate` |
| R5 | Region I | R1, R2b, R3b |
| R6 | Region II near-tip + macroscopic | R3b, R4 |
| R7 | Vacuum | R1, R2b, R3b |
| R8 | Assembly `theoremC15UpperInput_virasoro`, `IsFeasible.mono_T`, `t_*` expansion; E1 with O(1) | all |

Revisions made in this audit (cleaner implementation, checked against the TeX):
1. **Generalise in place, do not copy.** R3a and R4 reopen proofs that are ours (`Upper/Design/PerturbPhi.lean`
   `iteratedDeriv_designDelta_le`, `Upper/Design/CombTransform.lean` `designProfile_sdvHypotheses`,
   `Upper/Design/DesignCombProps.lean` `combTail_K1a`, `Upper/Holes/Holes.lean` `hole_lower_K4`). State the general
   lemma (squared PC; N-free constants; Λ-form for an arbitrary comb, the internal `h_part` made public) and re-derive
   the existing declaration as a corollary with the same name and statement. No parallel copy under `Ramped/`.
   Only the new ramped-specific statements go in `Ramped/`.
2. **Hole product: finite and rational.** U* uses `c_fl` only through `c_fl > 0` (`C_mid² ≥ C_2/(8c_fl)`, N2R
   l.209). The seven other hole pairs give `∏ρ_k ≥ (1−C/n)·16647192576/23591176505` (= 0.70565…, recomputed exactly;
   TeX issue 136 verified). No Euler product identities in Lean. TeX: replace the infinite product display by the
   finite one (R4 makes this edit).
3. **Reuse the design-side packages now on master.** R5 reuses `Upper/Positivity/RegionOne*` (case split and
   `airyWindowProd` sign/zero facts, `Window/AiryProdPositive`, `Window/LemmaR`); R7 reuses the `Vacuum*` assembly
   pattern and `Window/CardyWindow` (two-sided A_V still to add); R2b reuses `lemma_ID` (exact identity, any site and
   height sequences) and Prop 1.1.
4. **Uniformity in d.** State S5–S9 for all `d ∈ [0, min(1,(a_1−a_2)/8)]` and all `C_I, C_mid ≥ 1` (TeX l.173–177),
   so that the general-weight bump route (target D) can reuse them.
5. R2b fallback only if blocked: a named `CombToAiryInput` with the literal TeX quantifiers and a non-vacuity theorem.

**B. Σ at Virasoro** (from the `sn_u5t2` sketch; constructions in `spectral_rigidity.tex` `sr:Sigma`):
- Σ1 profile window class `𝒟x` (per-site heights, one displaced finite site) packaged as `Window` (S, from
  `profW`, `profV_*`, `pUnif_bound`, template `designWin`).
- Σ2 `DisplacedFamily`: sites `a_n + e`, heights → 0, `d = −κ`; `pi_nonneg` needs `profV_identity` for `d < 0`
  (`Π_n(d) = Π_n(0)(1+κ/|a_n−a_1|)`), `pi_lower` from `designFac_tail_lower` with `j ≠ n` (S–M).
- Σ3 Property (P) for `𝒟x`: generalise Lemma R, Prop I, Lemma W/ID, Prop V and K7 from the global-η class to
  profile windows (M–L). **Do in place** as in A.1: the design-side theorems take a profile, `designClass` becomes a
  special case. Shares Region I/vacuum machinery with R5/R7; schedule after R5/R7 statements are fixed.
- Σ4 `OmittedFamily` (`f ≥ 2`, first `f−1` sites omitted): general-`f` quadrature and Lemmas V/E/G, Lemma Z for
  modified sites, Property (P) for `f ≥ 2` (L). First a scout: does `sr:Sigma` need the omitted family, or does a
  displaced family with `e` large enough replace it?

**C. N = 1 super-Virasoro (`n1SuperVirasoroProblem`, `w = 1`, `μ = (1/2,1/2)`).**
- C1 done: `FixedWeightBand.n1_lowerBoundInput`, `n1_T_V_lower` (unconditional).
- C2 (scout, then M): generalise the upper/design side from `virasoroProblem` to every `w = 1` problem (15 files in
  `Upper/` mention `virasoroProblem`; `Q` should enter only through `V`, `g_vac` and the Cardy window). This gives the
  N=1 two-term law and Σ₀ (`n1:T3`), and A at N=1 once A is done.

**D. Later, not scheduled:** designs and bump at general `(w,Q)` (`w > 1`, W1.4); real `w ≥ 1` and N=(2,2)
(the abstract framework allows real `w`; plug in through the W1–W4 interface); two-level Clark curve
(`virasoro_two_level.tex`); continuous spin (`spinning_dual.tex`). **Out of scope:** the sharp five-term expansion
C15/ctu.5, integer spin (computer-assisted), the fold-tip theorem FT/FT-2E (Appendix D; the Lean route replaces its
compactness step by `teb:quant_c1_hb`, `lower_o1_two_edge.tex` l.931, and uses only Proposition P, which is done).

## 3. Schedule (at most two Sonnet agents; stop launching below 2.5 GB free disk)
1. R3a ∥ R4 (both generalise our own Design/Holes files; disjoint files).
2. R2b, then R3b, alongside C1 (Haiku).
3. R5 ∥ R7, then R6, then R8. C2 scout when a slot is free.
4. Σ1, Σ2, then Σ3 (after R5/R7), Σ4 scout.

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
- Fold-tip FT moved from Paper I to Paper II (QIprojects `45564ae42`). Paper I's plan defers it; it stays out of
  scope here too (§2 D). `TwoEdgeBootstrap/FoldTipSeed.lean` (seed lemma) is Paper I's and is unaffected.
- Shared files: the umbrella `FormalResearch/ModularBootstrap.lean` and `THEOREM_MAP.md` (targeted edits after
  merging `origin/master`; never apply an agent's stale umbrella as a diff).
