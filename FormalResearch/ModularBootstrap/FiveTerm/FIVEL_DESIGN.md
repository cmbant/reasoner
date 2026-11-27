# FIVE-L design note (sharp lower bound for the five-term expansion)

Work package FIVE-L of `PLAN.md`: `cts:edge-hankel` (C5), `cts:cauchy-dual` (C6), `cts:rosc-uncond` (C7),
`cts:boas` (C8), `cts:lower-main` (C9), `ctl:dyadic`, `ctl:pass2`, `ctl:freeze`, and the inputs `rem:corL`,
`rem:thmOloc`, `teb:quant_c1_near`.  All new files are `FiveTerm/Lower*.lean` (no existing file is edited).
Sources: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex` (§`cts:s5`), `constant_term_lower_log.tex`,
`five_term_roadmap.tex` (§`app:gp-lower`), `remainder.tex`, `recalled_paper1.tex`.

This note is rewritten (not appended to) as slices land; the "Status" table at the end is current.

## 1. Shape of the proof (what the paper does)

`cts:lower-main` is a contradiction argument.  A weakly feasible test `g` whose largest sign change `t_1(g)` is
`K c'^{-1} log c'` below the five-term value has Langer-chart displacement
`ũ_1(g) - φ_c(a_1) >= (K/2c_*) c'^{-4/3} log c'`, where `φ_c = û^{-1}` is the inverse of the *shifted Airy chart*
`û(ũ) = ũ + 2^{-2/3} c'^{-1/3} ψ_ε(2^{2/3} c'^{-2/3} ũ)` produced by `cts:cauchy-dual`(1).  Then

1. **Localisation** (Theorem J + `teb:quant_c1`, no compactness): `|ũ_1 - a_1| = O(c'^{-1/3})`.  *In Lean already:*
   `theoremJ_Delta_best`, `theoremFTLFW_oneZero_of_YVFor` (the bound `u_T - a_1 <= K_0 c'^{-1/3}` is inside its proof),
   `teb_quant_c1_typeII`, `QuantC1B2Holds`.
2. **Cauchy duality** (C6, with C5 as input): for every test, a `sigma`-invariant Cauchy identity on the half-disc `Omega`
   turns the slit integral into the edge pairing with `K_edge^eps`; the CFU/steepest-descent analysis of `K_edge^eps`
   gives the Airy-window form and the outer-band form.
3. **Oscillatory pairing at a good circle** (C7, `ctl:dyadic`, `ctl:pass2`): `P_R(H) + g_vac/2pi + (band tail) = O(...)`.
4. **Boas positivity** (C8, `ctl:freeze`): the band tail is `>= -O(c'^{-4/3} log c')`.
5. **Slope** (`rem:corL`(b), `teb:quant_c1_near`): `P_R(H) >= (K/32 L_* c_*) c'^{-4/3} log c'` from the first node alone.

Steps 2-4 are the analytic content (all of C5-C8 and the two `ctl` pieces); steps 1 and 5 and the final contradiction
are bookkeeping around inputs that Lean has (`teb_quant_c1_typeII`) or that are small (`teb:quant_c1_near`, `rem:corL`).
The reduction of the dimension statement to a *phase* statement (`gp:L`, `eq:gp-five-terms`) is generic in the constants
`(c_0, gamma_0)`: FIVE-U proved the upper conversion (`UpperPhaseChart.dimension_le_of_phase_le`); the lower conversion is
`LowerPhaseChart.dimension_ge_of_phase_ge`.

## 2. What each label takes as input; genericity

| label | takes (paper) | Lean inputs available | generic in |
|---|---|---|---|
| `cts:edge-hankel` (C5) | Lemma G strip bound, `V` two-term expansion, DLMF 10.17.5-6 two-term `J_0` | `lemmaB_d_sup` (weaker `c'^2`), `besselV_comparison`, `besselI0C_sector_asymptotic` (leading term only) | `prob` (the `V`, `Q` change with `(w,Q)`; table `ctu:s4`) |
| `cts:cauchy-dual` (C6) | C5; `esd:phase` potential `Phi_0`; the map `D_* -> Omega`; `G_outer`; CFU; `airy-id` | `Upper/Saddle/EdgePhaseZero` (SD_0), `FiveTerm/Virasoro*` (`Gout`, `gout_coupling`), `SignUncertainty/CtAiry*`, `CtCfu*`, `CtChart*`, `CtSd*`, `CtOuterBand*` (Paper I, other phase) | `OuterDatum W K g1 G` for everything after the amplitude |
| `cts:rosc-uncond` (C7) | C6; Theorem D; good circles; Props L, X_V; TE.1, TE.2 | `Special/AiryCftDefect` (Thm D), `ConcreteBootstrap/*` (good circles, quadrature), `FixedWeightBand/BandBoundW*`, `StripBand/*` | `prob` |
| `ctl:dyadic`, `ctl:pass2`, `ctl:freeze` | C7(1),(2); TE.2(1) quadrature; Prop L | `teb_bootstrap*`, `HankelBoot*`, `Contour/*` | `prob` |
| `cts:boas` (C8) | C6 Step 1, strip geometry of `zeta(b)`, Poisson-Jensen on `D_*`, Boas kernel | `FixedWeightTip/PoissonJensenGeneral` (complex PJ) | `prob` and `h` abstract (Step 3 core is a statement about any holomorphic `h`) |
| `cts:lower-main` (C9) | C6-C8, `ctl:*`, `rem:corL`(b), `teb:quant_c1_near`, Theorem J | `theoremJ_Delta_best`, `FiveTerm/*` constants | generic in `(c_0, gamma_0)`; Virasoro instance `(c0Star, gamma0)` |

**Genericity decision.**  The conversion layer (`LowerPhaseChart`) and every statement that only sees the outer datum
through `(c_0, gamma_0)` (the reference point `phi_c(a_1) = a_1 - (c_0/c_*) c'^{-1/3} - gamma_0 a_1 c'^{-1} + O(c'^{-4/3})`)
are stated for arbitrary reals `(c_0, gamma_0)`.  Statements about the transported test use `FixedWeightTip.psiTilde prob`
(general `prob`) where the existing Lean API is `prob`-generic (`lemmaQ_general_*`, `proposition_YV_W`), and
`virasoroPsiTilde` only where the API is Virasoro-only (`ConcreteBootstrap`).  The abstract analytic cores (Boas
residue identity, dyadic sums) are stated for arbitrary holomorphic data and are `prob`-free.

## 3. Audit of the three inputs

* `rem:corL` (packaged `C^1` stability and envelope): (a) is `lemmaQ_part2` (`virasoroPsiTilde_typeII_envelope`, with
  `varsigma_c = virasoroSigma c'`); (b), (c) (derivative bound, slope) are `QuantC1B2Holds` for violators (`teb_quant_c1_typeII`,
  `quantC1B2_secant_lower`); (d) with `K_0 c'^{-1/3}` (stronger than the stated `c'^{-1/3} log c'`) is the bootstrap output
  `hK_le` in `theoremFTLFW_oneZero_of_YVFor`.  The *convergence* clause of (c) (`Psi -> f_*/(2 L_*)` in `C^1`) is not exported by
  Lean (it is an intermediate step of the normal-families proof); no later step of FIVE-L uses it.  **Not large**, a repackaging.
* `rem:thmOloc` (Airy translates satisfy the local conditions): **not on the critical path of `cts:lower-main`**: it is the
  remark showing that disc-local methods stop at `log c`; nothing in C5-C9 cites it.  Elementary (`E(x) = g'^2 + x g^2`,
  `Ai(0)` value, DLMF 9.7.15 lobe bound); provable independently.
* `teb:quant_c1_near`: statement as in the paper is **true as stated** (proof sketch in the paper: it is TE.0' (1),(3) with
  `d_c = K_1 c^{-1/3}`).  In Lean it needs a copy-adapt of the `QuantC1Airy` normal-families argument with the hypothesis
  `a_1 < u_T` replaced by `a_1 - K_1 c^{-1/3} <= u_T` (only the limit threshold `>= a_1` is used there).  It is needed only when the
  sign of `c_0^*` is unknown: for Virasoro `c_0^* < 0` (not yet proved in Lean, `c0Star < 0` is a ~100-line numerical fact)
  gives `phi_c(a_1) > a_1`, and the violator form suffices.

## 4. Size and risk (honest)

PLAN's L estimate (25-30k lines) is realistic.  Not in Lean and large: (i) the b-plane/z-plane transport of the slit-strip
(`w = cosh(pi b)`, `z = zeta_D(b)`) with boundary values of `G(b)` on the slit and on `E_pm` (FiveTerm works on `Omega`
abstractly through `OuterDatum`); (ii) two-term complex Bessel asymptotics; (iii) the CFU chart and uniform complex Airy
window analysis for the *Paper II phase* `phi(v;x') = (4 pi/3) int_0^v (F(u) - x') du` (Paper I has the analogous stack for the
Hankel phase; the abstract parts `sd_eval`, `outer_band`, `stat_phase`, `morse_expansion`, `scalar_ift` are reusable); (iv) the
strip geometry of `zeta(b)` and the growth bound `h-growth` of C8 (Noshiro-Warschawski, Poisson-Jensen majorants); (v) the half-disc
Poisson machinery and good-circle selection of C7.  No input is false as stated; no paper statement was found false.

## 5. Delivery order (slices)

Delivered (all built under the lock, axioms `[propext, Classical.choice, Quot.sound]`, listed in
`/home/user/scratch/lean/agent_fivel_modules.txt`):

1. `LowerPhaseChart`: `dimension_ge_of_phase_ge` (unconditional chart conversion, generic in `(c_0, gamma_0)`), the named
   hypothesis `LowerPhaseStatement` (= `gp:L`, generic in `prob`), `delta_best_ge_of_phase`, and `spinless_lower_of_phase`
   (lower half of `thm:spinless-expansion`, conditional on `gp:L`).
2. `LowerCorL`: `corL_virasoro` (`rem:corL` packaged at Virasoro, unconditional).
3. `LowerSign`: `c0Star_neg` (`c_0^* < 0`), so `teb:quant_c1_near` is not needed at Virasoro.
4. `LowerBoasResidue`: the abstract core of `cts:boas` Step 3 (`boas_residue_identity`, `boas_local_lower`,
   `boasTop_norm_le`, `boasVert_norm_le`), `prob`-free.
5. `LowerDyadic`: the exponent bookkeeping of `ctl:dyadic`, `ctl:pass2`, `ctl:freeze` and the Boas rectangle
   (`pass2_exponents`, `gauss_window_exponents`, `gauss_top_le`, `gauss_vert_le`, `top_edge_exponent`, `dyadic_term_le`,
   `markov_select`).
6. `LowerEdgeHankel`: `cts:edge-hankel`(1) at Virasoro with absolute constants (`edge_hankel_exp_small` generic in `prob`,
   `edge_hankel_integral_sharp`, `edge_hankel_sup_sharp`, bundle `edge_hankel_one_virasoro`).

7. `LowerBesselTwoTerm`: the two-term complex Laplace asymptotic of `I_0`, `besselI0C_two_term`
   (`‖I_0(w) - e^w/√(2πw)(1 + 1/(8w))‖ ≤ 70 e^{Re w}|w|^{-5/2} + 2` for `Re w ≥ 1`): the Bessel input of `cts:edge-hankel`(2).
8. `LowerMain` (**skeleton, first deliverable after the 2026-11-26 plan change**): the structure `LowerMainInputs prob c0 γ0` whose
   fields are the open TeX lemmas as used in the proof of C9 (see the table of section 6), and `lowerPhase_of_inputs`:
   `LowerMainInputs prob c0 γ0` and `c0 < 0` give `LowerPhaseStatement prob c0 γ0 C` (Passes 1-2 `lower_pass_upper`, first node,
   Langer identification at `u_*`).  Every later module discharges or shrinks a field.
9. `LowerMainVirasoro`: `lowerPrelim_virasoro`, `lowerPhase_virasoro` and `spinless_lower_of_inputs` (lower half of
   `thm:spinless-expansion` modulo `LowerMainInputs`).

## 6. Status

Fields of `LowerMainInputs` (each is one open TeX lemma; nothing else is assumed):

| field | TeX | consumed by | to discharge it |
|---|---|---|---|
| `chart : LowerChart` | `cts:cauchy-dual`(1): shifted Airy chart `φ_c = û⁻¹`, `φ_c' = 1+O(1/c)`, `φ_c(a_1)` expansion | `lowerPhase_of_inputs` (reference point `u_*`, monotone chart) | CFU chart of the Paper II phase (`FctChart.cfu_chart_core`, `FctCfuTheta.cfu_chart`, `CtChartIft`, `CtChartInverse`, `CtSdEval`) + `LowerEdgeHankel`, `LowerBesselTwoTerm` (C5) + `Special/Airy*` |
| `combined : LowerCombined` | `cts:rosc-uncond`(4) combined dual identity (4a) general, (4b) under the pass-1 hypothesis | `lower_pass_upper` | Cauchy duality on `Ω` (C6 identity, `CtDualId`), `CtRoscUpper.airy_halfdisc_rosc`, `CtRoscEta.ctEta_ge_half`, `CtRoscDefect.airy_defect_identity`, `Special/AiryCftDefect` (Theorem D), `ctl:dyadic` (band moments), `LowerDyadic` |
| `pass2 : LowerPass2` | `ctl:pass2` | `lower_pass_upper` (pass 2) | second good circle at the sharpened scale (`CtDyadicRadius.markov_lintegral`, `LowerDyadic.pass2_exponents`, `markov_select`) |
| `boas : LowerBoas` | `cts:boas` (Steps 1-2 and the Gaussian assembly) | `lower_pass_upper` | `LowerBoasResidue` (`boas_local_lower`, `boasTop_norm_le`, `boasVert_norm_le`), `LowerDyadic.gauss_*`, `CtBoasAverage`, `CtBoasTent`, `CtBoasFreeze.boas_freeze_block`, `CtBoasAssembly.boas_ineq_tent`; conformal coordinate `ζ(b)` and `h-growth` still to build |
| `langer : LowerLangerPhase` | `cts:langer` / Theorem L*: `-ũ = β c^{2/3} τ(x)` on the real band (the `ũ ↔ τ` bridge) | `lowerPhase_of_inputs` | identify `A(b-ξ_*)^{3/2}` of `lemmaGPotentialInput_virasoro` with `N(x)` (`Upper/Comb`) |

Already-proved inputs (not fields): `LowerPrelim` (`rem:corL`(b), `lemmaQ_part3`; `lowerPrelim_virasoro`), `LowerFirstGood` (`cts:rosc-uncond`(1), discharged unconditionally from chart on band via `LowerGoodMain.lowerFirstGood_of_chart_on_band`), `c0Star_neg`, `dimension_ge_of_phase_ge`. `ctl:dyadic`, `ctl:freeze` enter as sub-structures when `combined` and `boas` are split.

## 7. Paper I (`SignUncertainty`) Reuse Map (audited 2026-11-27)

No remaining `LowerMainInputs` field follows directly from Paper I without new Virasoro-phase proofs: Paper I's `ct_chart_complex_of_analytic`, `ct_rosc_book`, `ct_boas_concrete`, and `cfu_K_airy_beta` are instantiated specifically for the Hankel Bessel phase `τ₀(a)/θ_ε`, and Paper I's own `CtDyadicInputs.combined` in `CtLowerFinal.ct_lower` remains open (`CtDyadicCombined.ct_combined_of_pieces` splits it into 5 pieces, with only `trans` proved). However, substantial **phase-free** infrastructure in `FormalResearch/SignUncertainty/` is directly reusable:

| Paper II target / field | phase-free Paper I declarations (directly reusable) | Hankel-phase-specific in Paper I (must build Virasoro analogue) |
|---|---|---|
| `boas` (`cts:boas`) | `CtBoasAverage` (`integral_gaussK_sq`, `integral_gaussK_abs_le`, `gauss_moment_poly`, `block_average`), `CtBoasTent` (`tentRamp_*`, `tent_*`, `tentPartition`, `tentNode_*`), `CtBoasFreeze.boas_freeze_block`, `CtBoasAssembly` (`BoasPartition`, `BoasSetting`, `BoasInputs`, `boas_ineq_assembled`, `boas_ineq_tent`, `sum_block_errors_le`) | `ct_boas_concrete` / `boas_concrete_core` (`CtBoasEventual`, `CtBoasFinal`), `CtBoasMoments` (`ct_boas_moments_top`, `tail_chebyshev`), `CtBoasPlb*`, `CtBoasFar*`, `CtBoasLmin`, `CtBoasWindow`/`CtTaper` (all use `hankelHL`, `boasX`, `tau0`, `sFar`, `ctTaper`) |
| `chart` (`cts:cauchy-dual` (1)) | `CtChartIft` (`scalar_ift`, `scalar_ift_conj`), `CtChartInverse` (`ct_inv_chart`, `ct_inv_exists_unique`), `CtSdEval` (`sd_eval`, `norm_a_bounds`), `FctChart.cfu_chart_core`, `FctCfuTheta.cfu_chart` (once Virasoro phase is written in `ℓ - κ z + r(z)` form) | `ct_chart_complex_of_analytic` (`CtChartComplex`), `cfu_K_airy_beta` (`CtSdMain`), `CtCfu.{NF, AF, dF}`, `CtOuter.outerTheta` |
| `combined` (`cts:rosc-uncond` (4)) & `pass2` (`ctl:pass2`) | `CtDualId` (`vertical_lines_eq_cts`, `strip_integral_zero`, `re_half_line_zero`), `CtRoscUpper` (`airyUpE`, `airy_halfdisc_rosc`), `CtRoscEta.ctEta_ge_half`, `CtRoscDefect.airy_defect_identity`, `CtRoscChart` (`holo_reflect`, `deriv_im_eq_zero_of_real`), `CtDyadicRadius.markov_lintegral` | `ct_rosc_book` (`CtRoscBookProof`), `CtRoscMass`, `CtRoscPos`, `CtRoscBudget`, `CtRoscAlg`, `CtRoscBound` (use `ctPhiC`, `ctFcC`, `hankelPsi`); `CtDyadicCombined` itself still has 4 open pieces in Paper I; `LowerPass2` has no Paper I analogue (Paper I's `ct:dyadic` (2) is unconditional at `O(c^{-1/3})` without Pass 1) |

| label | status | Lean |
|---|---|---|
| lower half of `thm:spinless-expansion` | proved modulo the structure `LowerMainInputs` (and no other hypothesis) | `LowerMainVirasoro.spinless_lower_of_inputs` |
| `cts:lower-main` (the contradiction argument, Pass 1, Pass 2, node slope, `ũ ↔ τ` arithmetic) | proved from the fields | `LowerMain.lowerPhase_of_inputs`, `lower_pass_upper` |
| `rem:corL` | proved at Virasoro | `LowerCorL.corL_virasoro` |
| `teb:quant_c1_near` | bypassed at Virasoro (`c0Star < 0`) | `LowerSign.c0Star_neg` |
| `rem:thmOloc` | not on the critical path | none |
| `cts:edge-hankel` (1) | proved at Virasoro | `LowerEdgeHankel.edge_hankel_one_virasoro` |
| `cts:edge-hankel` (2) | Bessel step proved (`besselI0C_two_term`); real three-term `V` expansion and assembly not done | `LowerBesselTwoTerm` |
| `cts:boas` | residue core proved, rest a field | `LowerBoasResidue`, field `boas` |
| `ctl:dyadic`, `ctl:pass2`, `ctl:freeze` | exponent bookkeeping and Markov selection proved; estimates are fields | `LowerDyadic` |
| `cts:cauchy-dual`, `cts:rosc-uncond` | fields | none |
