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

Not delivered, in dependency order (exact next steps in section 6): `cts:edge-hankel`(2), `cts:cauchy-dual`, `cts:rosc-uncond`
and `ctl:pass2` (analytic content), `cts:boas` Steps 1-2 and the Gaussian assembly, `cts:lower-main`, the `u~ <-> tau` bridge,
`teb:quant_c1_near`.

## 6. Status

| label | status | Lean |
|---|---|---|
| `rem:corL` | proved at Virasoro (item (d) with `c'^{-1/3}`, stronger than the paper; the `C^1`-convergence clause of (c) is not exported) | `LowerCorL.corL_virasoro` |
| `teb:quant_c1_near` | not formalised; true as stated; bypassed at Virasoro because `c0Star < 0` | `LowerSign.c0Star_neg` |
| `rem:thmOloc` | not formalised; not on the critical path | none |
| `cts:edge-hankel` (1) | proved at Virasoro (absolute constants; `G` is the defined Hankel integral, Hankel inversion not formalised) | `LowerEdgeHankel.edge_hankel_one_virasoro` |
| `cts:edge-hankel` (2) | NOT proved (two-term complex Bessel asymptotics) | none |
| `cts:boas` | Step 3 residue core proved (`prob`-free); Steps 1-2 (conformal phase coordinate, `h-growth`) and the Gaussian assembly NOT proved | `LowerBoasResidue` |
| `ctl:dyadic`, `ctl:pass2`, `ctl:freeze` | only the exponent bookkeeping and the Markov selection are proved; the analytic estimates are NOT | `LowerDyadic` |
| `cts:cauchy-dual`, `cts:rosc-uncond`, `cts:lower-main` | NOT proved | none |
| lower half of `thm:spinless-expansion` | proved only modulo the named hypothesis `LowerPhaseStatement` (`gp:L`); the conversion from phase to dimension is unconditional | `LowerPhaseChart.spinless_lower_of_phase` |

Exact next steps.
* `cts:edge-hankel` (2): the two-term expansion `J_0(z) = e^{i pi/4} e^{c'L}/sqrt(2 pi z) (1 + 3i/(32 pi x c'(v+i/2)) + O(|z|^{-2}))`
  uniformly for `arg z in (0, pi/2]`, plus the three-term `V(t(x))` expansion; `ComplexBessel/BesselI0Sector` (889 lines) has the
  leading term only and is the template.
* `cts:boas` Steps 1-2: `zeta(b) = (c'/(2 pi i))(Phi_0(b) + L(b))` on `D_*^-` and its univalence (Noshiro-Warschawski, not in Mathlib),
  then the complex Poisson-Jensen bound on all of `D_*^-` (Lean has `stripPoissonJensen_complex_general` only at tip points
  `|z - sigma_*| <= 0.1`), giving `h-growth`.  Step 3 then combines `boas_local_lower`, `gauss_top_le`, `gauss_vert_le`.
* `cts:cauchy-dual`: the `b <-> z` transport (`w = cosh(pi b)`, `z = zeta_D(b)`), then the CFU / steepest-descent stack for the
  Paper II phase, reusing the abstract parts of Paper I (`sd_eval`, `outer_band`, `stat_phase`, `morse_expansion`, `scalar_ift`).
* `ctl:dyadic`, `ctl:pass2`: the strip-band reduction of Proposition C7a (van der Corput, `teb:kernel`) and the sine-pairing
  estimates; the measure of `{r in [r_0, 2 r_0] : |sin(2 r^3/3 + pi/4)| >= 1/2}` (about `7/18 r_0`) feeds `markov_select`.
* `teb:quant_c1_near`: copy-adapt `QuantC1Airy` (about 1300 lines), replacing `a_1 < u_T` by `a_1 - K_1 c'^{-1/3} <= u_T`.
  Needed only if the sign of `c_0^*` is unknown, which is not the case at Virasoro.
* The `u~ <-> tau` bridge: the exact relation between `virasoroDeltaChart` and `cumulN` on the band, linking the Airy-chart
  displacement to `LowerPhaseStatement`.
