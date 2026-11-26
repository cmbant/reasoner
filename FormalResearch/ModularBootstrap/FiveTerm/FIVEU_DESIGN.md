# FIVE-U design: the sharp upper bound by the exact comb with smoothing

Scope: PLAN.md row FIVE-U (`cts:smooth-env`, `cts:tip-shared`, `cts:upper-design`, `cts:regionII-floor`,
`cts:shifted-langer`, `pm:tip-match`, `cts:upper-vac`, `cts:transfer` upper half, `thm:spinless-expansion` upper
half). New files only, all in `FiveTerm/Upper*.lean` (no new directory, no existing file edited). Source:
`CFT/modular_bootstrap/paper/constant_term_slit_strip.tex` (Lemmas C10-C15), `five_term_roadmap.tex`
(`app:gp-construct`...`app:gp-assembly`), `modular_bootstrap_gap_proof.tex` (reduction to a phase threshold).

## 1. What the upper bound is, and where the work is

The test is `g = (h_0 - H h_0)/2`, `h_0 = E_delta B_D`: `E_delta` is the strip form of `F_delta = m_delta F_*`
(`F_*` the exact minimiser of `cts:main`, `m_delta` the square-root regulariser, `delta = K c'^{-1} log c'`),
`B_D` a Blaschke comb with a real first zero at Airy position `|a_1| + d`, Airy-phase sites for `k <= N_split`,
shifted CFU quantiles for `k >= 2 N_split`, and every site `k >= 2` split into a conjugate pair whose height follows
the phase-locked detuning `R_delta`. The assembly (`app:gp-assembly`) has three parts.

* **A. Phase-to-dimension and choice of `d` (pure real analysis).** Choose `d` from the vacuum expansion
  `V/F_c = -d + (c'^{-1/3}/c_*) B[F_delta] + O(c'^{-4/3} log c')`, check `g_vac > 0`, feasibility at
  `t(chi_1') + C c'^{-1} log c'`, convert the first-site phase through the Langer chart.
* **B. The constants:** `J[F_delta] - c_0^* <= C delta^2`, `B[F_delta] = -alpha_tip delta/2 + O(delta^2)`
  (`cts:smooth-env` (1)).
* **C. The estimates (U1)-(U4)** behind the family: membership and the vacuum identity of `h_0` (K7 with an
  envelope), Region II (branch-cut-wrapped saddle descent, product comparison on the hole), Region I (Laplace-Airy
  representation, shifted Langer identity, quantile and pair-height bookkeeping), the vacuum expansion with the
  tip-dipole cancellation `pm:tip-match`.

A and B are done (section 3). C is the bulk of the work and is **not** done: it is the content of C11-C14.

## 2. Interface decisions (generic in `(W, K, g_1, G)`, and in the source)

* The outer-function side is `OuterDatum W K g1 G` (FIVE-0). Every lemma of B takes it as a hypothesis, so
  Virasoro is the instance `gout_outerDatum_g1Out` (with `g1Out = g1Vir`) and the fixed-weight case needs only another
  datum (FIVE-W: the datum for `(w,Q)`, `g1`, `g3` from `ctu:jets`).
* The source side is `ShiftSource` (PM-0), not `FixedWeightProblem`: `T_V`, `Delta_best`, `IsFeasible`, `TestClass`
  exist for it, `ShiftSource.ofProblem` embeds `FixedWeightProblem` with `rfl` bridges, so `FixedWeightProblem` and
  PM mixtures are instances and no duplicate is needed. Everything in A is stated for an arbitrary `src : ShiftSource`.
* The five-term constants enter only through `(c_0, gamma_0)` (`c0StarOf g1`, `gamma0Of g1 g3`; Virasoro `c0Star`,
  `gamma0`), so the chart conversion is generic in two reals (`dimension_le_of_phase_le`).
* **The interface between A and C is the Prop `SharpUpperFamily src W K G g1 gamma0`** (`UpperAssembly.lean`): a family
  `g(c', d)` with (U1) test-class membership, (U4) the vacuum expansion, (U2)-(U4) positivity beyond
  `t(chi_1(c',d)) + C_1 c'^{-1} log c'`, and the first-site phase relation `eq:gp-first-site`. Constants `K_delta, C_V,
  C_1, C_tau` are independent of the shift range `D`; only the threshold depends on `D`. Each lemma of C proves some
  fields of it for a concrete construction; the construction itself (`E_delta B_D`) is the next design step, not yet
  made (see section 4).
  This is a named hypothesis of the paper's own reduction (`gp:U`) split into its estimates, not the conclusion:
  the conclusion is the dimension-level expansion, and the choice of `d`, the sign of `g_vac`, feasibility and the
  chart inversion are proved from the fields.

## 3. Delivered slices (all `lake build`, axioms `[propext, Classical.choice, Quot.sound]`)

| module | content | label |
|---|---|---|
| `UpperSmoothEnv` | `fDelta`, `combB`; `fDelta_hAdm` (`F_delta in H_adm`, `F_delta'(0) = -g1 - delta/2`), zero-free, `F_delta(0)=1`, `0 <= J - c0 <= 25 alpha_C delta^2`, `B[F_*] = 0`, `|B[F_delta] + alpha_tip delta/2| <= 25 alpha_C delta^2`; Virasoro instance `smooth_env_one_virasoro` | `cts:smooth-env` (1) |
| `UpperPhaseChart` | `tauPhase`, `dimension_chart_expansion` (`|Delta - (c/Lambda_V + (2 xi/3) c eps + K_2 c eps^2)| <= 6 c eps^3`), `phase_poly_bound`, **`dimension_le_of_phase_le`**: `tau(x) <= tau_* + C c^{-2} log c  =>  c/12 + c x^2/3 <=` five-term `+ C_+ c^{-1} log c`, generic in `(c_0, gamma_0)` | `gp:E5`, end of `eq:gp-upper-final` |
| `UpperTipMatch` | `tip_match` (unconditional): the slit coordinate expansion from `cosh(pi x) = sqrt2 (1+y^2)/(1-y^2)`, `kTip = 32 (sqrt Y)^3/(9 pi^2)`, and the tip-dipole estimate `O(c'^{-1} (lambda S)^{1/2})` in the paper's variables, `kappaComb` (`kappa^{3/2} = 3 pi/2`) | `pm:tip-match` (C14_0) |
| `UpperDetuning` | `fStar_edge_eq` (`K F_*(e^{-i psi}) = q F_*(iy)`, generic in the datum), `fDelta_edge_ratio` (`|F_d(iy)+K F_d| = D_d |F_d(iy)|`, `|K F_d| = R_d |F_d(iy)|`), `detuneD_bounds` (`1 < D <= 1+R`, `R/10 <= D-1`, `D <= 1+sqrt2`), `detuneR_pow4_bounds`, `1+sqrt2 < cosh(pi/2)` | `cts:smooth-env` (3), `R_delta`, `D_delta` |
| `UpperPairPhi`, `UpperPairTaylor`, `UpperPairDrift`, `UpperPairGamma`, `UpperTipSharedD` | `pair_cancel`, `ScaleHyp.taylor`, `pair_drift` (b1, explicit constants, with weight-jump terms), `pair_drift_gamma` (b2), `tipShared_d` | `cts:tip-shared` (b1), (b2), (d) |
| `UpperMainInputs` | skeleton: `UpperMainInputs` (fields `c11_membership`, `c11_first_site`, `c12_regionII`, `c13_regionI`, `c14_vacuum` over an abstract comb `h0`; the test is `upperTest = pairOdd u (hankelTransform w u)`), `sharpUpperFamily_of_inputs`, `sharp_upper_of_inputs`, `spinless_upper_of_inputs`; concrete open statements `AiryLinearMoment` (tip-shared (a)), `AiryPrimitiveDecay` (tip-shared (c)) | skeleton |
| `UpperAssembly` | `SharpUpperFamily`; **`sharp_upper_of_family`** (any `ShiftSource`) and **`spinless_upper_of_family`** (`Delta_best <= ... + c0Star + c1Langer c^{-1/3} + d2Star c^{-2/3} + C c^{-1} log c`) | `cts:transfer` and `thm:spinless-expansion`, upper half, **modulo `SharpUpperFamily`** |

## 4. What remains (all inside `SharpUpperFamily`), in the paper's dependency order

Sizes are estimates from the existing O(1) analogues (`Upper/Ramped`, 21k lines for W-P6; K7/SD/Hankel 11k).

1. `cts:smooth-env` (2)-(3): strip factorisation of `E_delta` on `|Im b - 1/2| <= 1/16`, potential `Delta Phi_delta`,
   branch point `i(1/2 + eta_delta)`. Input not in Lean: the paper takes `G_outer = (1+z^2)^{-1} H_3^{1/4} tilde G`
   from `cts:cauchy-dual` Step 2 (FIVE-L); the Lean `Gout` is built differently (`hbarA`, `qBd`), so the strip bounds
   must be re-derived from `Gout`. About 2-3k lines. The algebraic half of (3) (`R_delta`, `D_delta`, `1 < D_delta <=
   1+sqrt2`) is done (`UpperDetuning`); the `x`-derivative bounds of (3) are not.
2. `cts:tip-shared` (a)-(d): (a) Airy linear moment (Hadamard product of `Ai`, DLMF 9.7.5; `Special/AiryCft2DerivHadamard`,
   `AiryAsymZeros` are the inputs), (b1)/(b2) pair-drift cancellation (elementary Taylor, 1k lines), (c) Airy primitives
   `B`, `C` and the identity `cts:BC-id` (integration by parts, DLMF 9.7.9; needs `AiryAsym*`), (d) trivial. About 2.5k.
3. `cts:upper-design` (C11): (1) exact-CFU geometry of the shifted quantiles (`chi_k^sh`, `M_c` convexity), (2) Region II
   descent with the branch-cut loop, Region I secant Laplace-Airy representation with explicit error, (3) membership.
   The membership part is **K7 with an envelope**: `InnerCombHyp` demands `|B| <= 1`, `|B| = 1` on `E_+`, which `E_delta B_D`
   does not satisfy, so `Upper/Membership`, `Upper/Saddle`, `Upper/Hankel` need an amplitude-carrying generalisation
   (`TwoSaddleAmplitude` already carries an amplitude; the K7 wrappers do not). In-place generalisation of existing files
   is a follow-up for the lead (this agent does not edit them). 6-10k lines.
4. `cts:regionII-floor` (C12): hole comparison and Euler product for the pairs `k = n +- m`, `|T_{chi+i eps}|^2`
   monotone in `eps`, the quadratic phase-error positivity (trigonometric, `C_buf = 4(C_1 + C_2) + 1`). Existing:
   `Upper/Holes` (K4, K5, K6) at O(1). 4-6k.
5. `cts:shifted-langer` (C13): exact-CFU shifted Langer identity with the global tip kernel, `W_D^tip` bounds, `Pi_n`
   asymptotics via Euler's product, good Airy radius, Region-I positivity on cells `n_0 < n <= N_split`. Existing:
   `Upper/Window` (Lemmas G, V, E), `Upper/Ramped/RampedBumpRegionI`. 5-8k.
6. `pm:tip-match` (C14_0): **done** (`UpperTipMatch.tip_match`).
7. `cts:upper-vac` (C14): the vacuum sum over Airy window and band with the `x_split` dependence cancelling.
   2-4k. After it, instantiate `SharpUpperFamily` for Virasoro, which closes `spinless_upper_of_family`.

Total remaining: about 25-35k lines, dominated by items 3, 4, 5. No genuine blocker (every input exists or is
elementary); the blockers for a *session* are size and the K7-with-envelope generalisation.

## 5. Findings on the paper (no statement found false)

* `app:gp-assembly`: `K_+` is chosen larger than twice the vacuum-error constant, which is "uniform in `|d| <= D
  c'^{-4/3} log c'`", while `D` must contain `K_+` (`|d| <= (alpha_tip K_delta/c_* + K_+) c'^{-4/3} log c'`). This is
  non-circular only if the error constant is independent of `D` (the paper's "implied constants absolute once
  `c' >= c_0(..., D)`"). `SharpUpperFamily` records exactly this quantifier order (`C_V` before `D`).
* `thm:spinless-expansion` is stated for `Delta_best(c)` with `c' = c - 1`; in Lean the argument is `c'` throughout
  (`Delta_best c' = c'/12 + T_V c'`), which is the paper's convention in the supplement.
* `cts:smooth-env` (1) holds for every `delta in (0,1)` (not only `< delta_0`), with the absolute constant `25 alpha_C`.

## 6. Finding (K7 is not applied verbatim)

`cts:upper-design` (3) says K7 "applies verbatim" to `h_0 = E_delta B_D`. K7's hypotheses (i)-(ii) (analytic on
`|Im b| < 7/8`, `|B| <= 1` on `|Im b| <= 1/2`, `Phi_1` bounded with two derivatives on `|Im b - 1/2| <= 1/4`) fail for
`E_delta B_D`: `E_delta` has the branch point `i(1/2 + eta_delta)`, `eta_delta ~ delta`, inside that strip, and
`|E_delta|` is unbounded near it. What the Lean K7 chain really needs is the decay bound of the paper's five-piece
deformation (part (2)); `fwM_of_decay` (membership from decay) and the vacuum identity are independent of `InnerCombHyp`.
So the amplitude-carrying version is: take the decay estimate as the input of `c11_membership`, not re-derive it from
`InnerCombHyp`.
