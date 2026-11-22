# Paper J, Layer 4 phase B2: plan to prove `ParabolicCylinderFacts U V cPC CPC` for the actual functions

Scoping note, with the status of phase B1 below. Branch `lean/paper-j-layer4`; scoped at head `812de42`. Sources read: `Charts/ParabolicCylinder.lean`,
`Charts/SoftParabolicCylinder.lean`, `Charts/TransferCoefficients.lean`, upstream `bjbraams/lean-DLMF` @ `7edc630` (read-only, untrusted
data), `ThirdParty/lean-dlmf` (vendored: LG/Sturm closure and `Basic.{Functions,WeberEquation,Wronskians}`), `FormalResearch/Special`.
Numerics: mpmath 1.3.0, 40-60 digits, scratchpad only, not committed. "Consumed" below is a `grep` of `.field` in `JacobiEigenvectors/`.

## Status after phase B1 (what is true now)

* **Proved for the actual `pcU a z = Re U(a,z)`, `pcV a z = Re V(a,z)`** (no rescaling): `PCExactFacts` (`ode_U/V`, `wronsk`, `shift_*`, `reflect` for `a <= 0` with the Gamma bridge, `reflect_V`; `Charts/PCExact.lean`, `pcExactFacts`), `PCSmoothFacts`
  (`Charts/PCSmooth.lean`, `pcSmoothFacts`), `PCPhaseFact` (`Charts/PCPhase.lean`, `pcPhaseFact`).  All axiom-pinned to `[propext, Classical.choice, Quot.sound]`.
* **Statements changed** (findings, `PLAN.md` F-PC2, F-PC3): `phase_osc` is on the lattice `mu^2 = 2n+1` only (every consumer instantiates it; real `mu` needs the oscillatory Olver theory, unproved upstream);
  `smooth_U/V` are weakened to slice smoothness + joint continuity (what the consumers use).  No sign or constant error was found in `shift_*`, `reflect`, `reflect_V`, `wronsk`, `ode_*`: they are proved as stated.
* **Joint `ContDiff ℝ ⊤` of `(a, z) -> U, V` (paper's statement, not used)**: not proved.  Entire dependence in `z` and in `a` is vendored separately; Mathlib has no Osgood/Hartogs; the route is Kummer's series, jointly:
  either iterated-derivative bounds for `contDiff_tsum` on the terms `(alpha(a))_n z^{2n} / ((c)_n n!)` (polynomial in `a`), or an Osgood lemma (continuous + separately entire => Cauchy integral in `a` => jointly `C^1`, then induction on the order).  Estimate 500-800 L.
* **Phase B2, stage 1 (proved, banked; all axiom-pinned `[propext, Classical.choice, Quot.sound]`, umbrella builds):**
  * **E0** (`Charts/PCOrigin.lean`): explicit real initial values `pcU_zero, pcUD_zero, pcV_zero, pcVD_zero` (Gamma quotients); Wendel bound `Gamma_add_half_le`, `le_Gamma_add_half` (`y/sqrt(y+1/2) <= Gamma(y+1/2)/Gamma(y) <= sqrt y`, log-convexity);
    `Gamma_ratio_origin` (`7/25 sqrt k G1 <= G3 <= 7/4 sqrt k G1`, `k = k2 a 0`); origin envelopes with **absolute constants `1/2, 2`**:
    `origin_well_U`, `origin_well_V` (`a <= 0`, resonance-free via the reflection formula, `sin^2 + cos^2 = 1`), `origin_bar_U` (`a > 0`), and in the shape of the `PCEnvelopeFacts` fields at `z = 0`
    (`origin_env_well_U/V`, `origin_env_bar`, using `Ewell a 0 = Ebar a 0 = 1`); `pcU_zero_zero_pos : 0 < pcU 0 0` (sign anchor).  mpmath: `kappa E_U / M_bal in [0.88, 1.28]` for `a in [-300, 300]` (tends to `(sqrt2/sqrt pi)^{1/2} = 0.893` for `a -> -inf`, and to `1.000` for `a -> +inf`), V-part `1.00-1.27`.
  * **Decay of `U`** (`Charts/PCLaplace.lean`): the Laplace representation DLMF 12.5.1 for real `a > -1/2` (`pcU_eq_laplace`, own proof in real variables: moments `lapI`, `hasDerivAt_lapI`, `lapI_ibp`, `lapI_zero`, uniqueness `weber_unique` from `pc_wronsk`,
    initial values by Gamma duplication), `pcU_pos_of_gt` (`U(a,x) > 0` for `a > -1/2`, all `x`), `pcU_decay_bound` (`|U(a,x)| <= C (1+x)^n e^{-x^2/4}`, `x >= 0`, every real `a`, by `pcU_three_term`), `tendsto_pcU : U(a,.) -> 0`.
    The upstream route (12.5.1 / 12.9.1 in `EquationAndIntegrals.lean`) was not used; no ThirdParty edit was made.
* **Where stage 1 stopped, and the next step of each target:**
  * **(a) E0: done** for the `U` and `V` values at `z = 0`.  Next consumer: E2/E4 normalisation (`E_U(z)/E_U(0) in [c,C] A(z)/A(0)`).
  * **(b) `U_pos`: decay is proved; two short lemmas remain.**  (i) *no zero beyond the turning point*: for `x0 >= 2 sqrt(max(-a,0))` (so `p = x^2/4 + a >= 0` on `[x0, inf)`), `U(a,x0) != 0`.  Route (as upstream `CylinderRealZeros.no_zero_of_decay`, to be re-proved, ~40 L): `g = U U'` has `g' = U'^2 + p U^2 >= 0`; a zero at `x0` gives `g >= 0` on `[x0,inf)`, so `U^2` is monotone, tends to `0` by `tendsto_pcU`, hence `U = 0` on `[x0,inf)`, contradicting `pc_wronsk` (`U,U'` not both zero).  (ii) *sign*: `a |-> U(a, 2 sqrt(max(-a,0)))` is continuous (`pcSmoothFacts.cont_U`), non-vanishing by (i), `ℝ` is connected, and it is positive at `a = 0` (`pcU_zero_zero_pos`); then `U(a,.)` has constant sign on `[x0,inf)`.  Together: `U_pos`.
    Negative regression already in the plan: `U(-10,z)` has its last zero at `4.70 < 6.32`.
  * **(c) E1: not started** (stopped before it).  Chosen route unchanged (plan section 3, E1, E4): `exists_solution_exp_of_pos` with `f = p`; recessive identification now only needs `tendsto_pcU` (+ the Wronskian argument), which is proved.  First concrete lemma: the explicit variation bound `int_{z2}^inf |p^{-1/4}(p^{-1/4})''| <= C` for `a >= 1`, `z2 = 0`, i.e. the case with no turning point (plan item 7); then `env_bar`, `molv_bar` with E0's `origin_env_bar` as the normalisation at `z = 0` (the constants `[1/2, 2]` are absolute).  No numerical range was changed; the plan's constants (`cPC <= 0.631`, `CPC >= 1.79`, `A^{1/3}` floor) are unaffected.
* **Remaining special-function premise: `PCEnvelopeFacts U V cPC CPC`** (`cPC_*`, `env_well`, `env_bar`, `molv_well`, `molv_bar`, `V_growth`, `U_pos`, `beyond`), the B2 block of sections 3 and 5 below.  `ParabolicCylinderFacts.ofEnvelope` (`Charts/PCActual.lean`) turns it into `ParabolicCylinderFacts pcU pcV cPC CPC`.

## Next steps (proposed, at the merge of `lean/paper-j-layer4` to `master`)

Everything proved so far is on `master`; the work paused after phase B2 stage 1. Remaining, in dependency order (item numbers refer to section 5):
0. **Status (supersedes the numbered remainder below):** `PCEnvelopeFacts pcU pcV cPC CPC` and `ParabolicCylinderFacts pcU pcV cPC CPC` are proved for the actual functions with absolute constants, with only the restated `V_growth` (`z >= max(2 sqrt(max(-a,0)),1)`; Airy-hard near the turning point, consumed by no proof) as a hypothesis: `Charts/PCEnvelopeAssembled.lean`, `pcEnvelopeFacts_of_vGrowth`, `parabolicCylinderFacts_of_vGrowth`; the pieces are `PCPositive`, `PCEnergyWell`, `PCEnergyAiry`, `PCEnergyAiryEnv`, `PCEnvWellFar`, `PCEnvBar`, `PCEnvCompact`, `PCMolv`, `PCBeyond`. Open: `V_growth`; the other Layer-4 chart inputs (see below).
1. **`U_pos`: done** (`Charts/PCPositive.lean`: `pcU_ne_zero_beyond`, `pcU_pos_beyond` = the field `U_pos` for `pcU`; also `cont_pcUD`, `cont_pcVD`, joint continuity of the derivatives). Axioms `[propext, Classical.choice, Quot.sound]`.
1b. **E2 (oscillatory interval) and E3 (Airy zone) by energy arguments, no Liouville-Green** (`Charts/PCEnergyWell.lean`, `Charts/PCEnergyAiry.lean`, axioms `[propext, Classical.choice, Quot.sound]`; route found by the independent review): for `a <= -4`, `0 <= z <= z1Well a = 2 sqrt(A - 2 A^{1/3})`, the modified energy `H = E1 + alpha y y'` satisfies `H' = alpha' y y'`, giving `E1Well_bounds` (`80/99 E1(0) <= E1(z) <= 5/4 E1(0)`) and `env_well_on_Icc_U_V` (two-sided `env_well` for `pcU` and `pcV` on `[0, z1Well a]`, constants `43/100, 117/50`, from `PCOrigin`). On `[z1Well a, z2Airy a]` the constant-scale energy gives `R0Airy_bounds` (`exp(+-18)`); `env_well_on_airy_U_V` (`Charts/PCEnergyAiryEnv.lean`) gives the two-sided `env_well` for `pcU`, `pcV` on `[z1Well a, z2Airy a]` with constants `exp(+-14)`.
2. **E1 for `a >= 1`** (no turning point; item 6): explicit variation bound for `p^{-1/4}(p^{-1/4})''`, `p = z^2/4 + a`, for the vendored `exists_solution_exp_of_pos`; with the numerical negative regression of the plan. This is the main technical risk (Sonnet).
3. **E4 for `a >= 1`**: `env_bar`, `molv_bar` (item 7; recessive identification by `tendsto_pcU` + Wronskian; normalise at `z = 0` by `origin_env_bar`). Then `a in (0,1)` by compactness (item 9 part).
4. **Oscillatory, Airy and exponential zones for `a <= -A0`** (item 8, 3 rounds): `env_well`, `molv_well`, `beyond` (Sonnet; E2 finite-endpoint oscillatory LG, E3 regularised-energy bound, `|U'|` Riccati barrier).
5. **Constants and compact range** (item 9) and far-region `V` facts (item 10): joint continuity + positivity on the compact range; then `PCEnvelopeFacts pcU pcV cPC CPC` and, by `ParabolicCylinderFacts.ofEnvelope`, `ParabolicCylinderFacts pcU pcV cPC CPC`.
Parallel or later:
* `UpstreamFacts` structure (one field per assumed upstream statement, exact transcription, provenance, numerical check) only when a first real entry exists (none needed so far).
* Full joint `ContDiff` of `(a,z) -> U, V` (500-800 L, optional; consumers use the weak form).
* The other Layer-4 inputs (`PLAN.md`, Layer-4 list items 2-6): `BulkWeberChart`, `SoftEdgeChart`, `BulkPhaseInputs`, `TransferBundle`, the cover/mirror fields of `ChartInputs`, and `Layer4Inputs` for the truncated family; each needs the Weber envelope theorem above (the chart fields are estimates built on it) and the Casoratian-Volterra engine already proved.
* Satisfiability check (an explicit family with all hypotheses discharged) once `PCEnvelopeFacts` is proved.
* Paper side: the findings of `PLAN.md` (`delta > 0` in cor:eigen, right-chart start F-CC1, `StdDM`/(E_Kbar) in thm:B, `V_growth` F-PC1, lattice `phase_osc` F-PC2, weak `smooth` F-PC3, the fermion constant 8) for the next paper revision.

## 0. Summary

* The structure has 21 fields (`U_pos` and `beyond` included). 13 are consumed by a Lean proof (`cPC_*`, `smooth_*`, `ode_U`,
  `wronsk`, `reflect`, `reflect_V`, `env_well`, `env_bar`, `molv_*`, `phase_osc`). **Not consumed anywhere (8):** `shift_*` (4), `ode_V`, `V_growth`,
  `U_pos`, `beyond`. They are chart-level facts re-stated as `SoftEdgeChart` fields (`grow3`, `lb_pc`, `ratio2`, ...), so they never block the pipeline.
* Verdicts: 13 fields are exact identities or constants that follow from upstream (NOW or B1: `cPC_*`, `ode_*`, `wronsk`, `shift_*`, `reflect*`, via the
  real restriction) or need one new lemma (`smooth_*`, B1); `phase_osc` is DERIVABLE from our Hermite Plancherel-Rotach **only on the lattice
  `mu^2 = 2n+1`** (the field says all real `mu`: HARD as stated, but every consumer uses the lattice); `env_well`, `env_bar`, `molv_well`, `molv_bar`,
  `beyond`, `U_pos` are B2 (one new "Weber envelope theorem", the only large item); `V_growth` is **false as stated** (Finding 1).
* Upstream does **not** contain the uniform envelope estimates: 12.10.18-21 (oscillatory), 12.10.5-6 (V, `t > 1`), 12.10.35-38 (Airy) are unproved
  (`Uniform/ExpansionData.lean`, `TurningPoint.lean`); what is proved (`UniformLG`, `UniformLG2`: 12.10.3-4, 12.10.25, 12.10.29, 12.10.31) is for fixed
  `delta`, `mu -> infinity`, with unquantified normaliser `g(mu)` (`IsBigO`), and its closure (150k lines, 20 TauCeti imports, unproved upstream) is not
  vendorable. The reusable upstream tool is the *abstract* LG theorem set already vendored (`LiouvilleGreenReal`, `LiouvilleGreenFinite`).

## 1. Conventions: how our `U, V` relate to DLMF and upstream

`U V : ℝ → ℝ → ℝ`, `U a z = Re parabolicCylinderU (a:ℂ) (z:ℂ)`, `V a z = Re parabolicCylinderV ...` (upstream `DLMF.Confluent`, `Basic/Functions.lean`:
`U = U(a,0) u1 + U'(a,0) u2` = DLMF 12.4.1, `V = V(a,0) u1 + V'(a,0) u2` = 12.4.2, 12.2.8-9 with reciprocal Gammas, so `V` is entire in `a`).
**No rescaling; identical normalisation** to DLMF 12.2 and to the structure (`Wr{U,V} = sqrt(2/pi)`, `V = Gamma(1/2+a)/pi (sin(pi a) U(a,z) + U(a,-z))`).
Checked (mpmath, 40 digits): upstream series definitions equal `pcfu`, `pcfv` (`~1e-41`, `a in {0.3, -1.7, 2.2, -0.25, ...}`), and at `a = -1/2, -3/2`
(where mpmath `pcfv` fails and the classical formula has a pole) the series definition satisfies all of `wronsk`, `shift_*`, `reflect`, `reflect_V`
to `2e-38`. Reality: upstream `parabolicCylinderU_real`, `parabolicCylinderV_real` (`ElementaryProperties.lean` 170, 197, from `conj_*`) give `Im = 0`;
derivatives: Mathlib `HasDerivAt.real_of_complex`, so `deriv (U a) z = Re (parabolicCylinderUDeriv a z)`. Gamma bridge for `reflect` (all `a <= 0`, incl.
`cos(pi a) = 0`): `pi / Gamma(1/2+a) = cos(pi a) Gamma(1/2-a)` from `Real.Gamma_mul_Gamma_one_sub` at `s = 1/2 + a` (at `a = -n-1/2` both sides are `0`;
checked). It is false for `a = n + 1/2 > 0`, which is why `reflect` is stated for `a <= 0`.

Vendored now: `Basic.{Functions, WeberEquation, Wronskians}` (ODE, entire in `z`, `parabolicCylinderU_recurrence_add/sub` = 12.8.2/12.8.3, `parabolicCylinderU_wronskian_neg`,
`parabolicCylinderV_wronskian` = 12.2.10, `isWeberSolution_parabolicCylinderV`, `parabolicCylinderV_zero/VDeriv_zero` = 12.2.8-9, `parabolicCylinderD_nat` = 12.7.2, with
a local `hermite_add_two`). **Not vendored but cheap:** `Confluent/ParabolicCylinder/WronskiansAndConnections.lean` (475 lines; `parabolicCylinderU_neg_eq` = 12.2.15,
`parabolicCylinderV_neg_eq` = 12.2.16, `parabolicCylinderV_recurrence_add/sub` = 12.8.7/12.8.6). Its imports `Basic.Functions`, `Wronskians` suffice: I checked that none of the
13 declarations of its third import `EquationAndIntegrals` is used in the file (`grep`), so dropping that import is a one-line patch. Same for `ElementaryProperties.lean` lines ~104-225
(conj lemmas, reality, separate entire-ness in `a` and `z`): drop `Coulomb`, `Confluent.ParabolicCylinder` imports; to be confirmed by a build.

## 2. Field-by-field map

Verdict key: **NOW** = glue from vendored/own Lean; **B1** = exact identity, needs only the (cheaply) vendored basics; **B2** = needs new envelope estimates;
**HARD** = new theory. Sizes are Lean lines (L) for the new proof.

| field | statement (real variable) | source | Lean that gives it / why not | verdict, size |
|---|---|---|---|---|
| `cPC_pos`, `cPC_le` | `0 < cPC <= CPC` | universal constants | existential: chosen last. Numerics force `cPC <= 0.631`, `CPC >= 1.79` (Finding 5) | NOW, 0 L |
| `smooth_U/V` | `ContDiff ℝ ⊤ (p ↦ U p.1 p.2)` | entire in `(a,z)` | upstream: entire in `z` (vendored) and in `a` (`parabolicCylinderU_entire_order`, `ElementaryProperties` 124) **separately**; `ParamHolomorphic` also separate. Mathlib has no Osgood/Hartogs. Joint smoothness needs a new lemma (series `u1,u2` = `exp(-z^2/4) M(alpha(a), b, z^2/2)`, `(alpha)_k` polynomial in `alpha`, locally uniform majorant, `contDiff` of `tsum`; or Cauchy integral in `a` over a circle). Consumers use only: continuity in `(a,z)` (`WindowMass` 473), smoothness in `z` for fixed `a` (`BulkPhasesPC` 138, `WindowEnvelopes` 760, `SoftTransfer` 577). A weaker Prop `(∀ a, ContDiff ℝ ⊤ (U a)) ∧ Continuous (uncurry U)` would be B1-easy | B1, 250-450 L (150 L for the weak form) |
| `ode_U`, `ode_V` | `y'' = (z^2/4 + a) y` | 12.2.2, 12.2.4 | vendored `deriv_deriv_parabolicCylinderU`, `isWeberSolution_parabolicCylinderV` + real restriction | NOW, 60 L |
| `wronsk` | `U V' - U' V = sqrt(2/pi)` | 12.2.10 | vendored `parabolicCylinderV_wronskian` (`Re`, imaginary part `0`) | NOW, 30 L |
| `shift_U_up/dn` | `U' + z/2 U + (a+1/2) U(a+1) = 0`; `U' - z/2 U + U(a-1) = 0` | 12.8.2, 12.8.3 | vendored `parabolicCylinderU_recurrence_add/sub` | NOW, 30 L |
| `shift_V_dn/up` | `V' - z/2 V - (a-1/2) V(a-1) = 0`; `V' + z/2 V - V(a+1) = 0` | 12.8.6, 12.8.7 | `parabolicCylinderV_recurrence_sub/add` (WronskiansAndConnections 363-460, proofs by `IsWeberSolution.eq_zero` and Gamma functional equation) | B1, 40 L (+ extraction) |
| `reflect` | `U(a,-z) = -sin(pi a) U + cos(pi a) Gamma(1/2-a) V`, `a <= 0` | 12.2.15 | `parabolicCylinderU_neg_eq` (all complex `a`) + Gamma bridge of section 1 | B1, 50 L |
| `reflect_V` | `V(a,-z) = cos(pi a)/Gamma(1/2-a) U + sin(pi a) V`, `a <= 0` | 12.2.16 | `parabolicCylinderV_neg_eq`, no bridge needed (`Gamma(1/2-a)` is the same symbol). Sign check: residual `2e-38` at `a in {0,-0.5,-1.5,-0.3,-2.2,-6.5,-9.9}`, `z in {-2.3,0.4,1.9,3.3}`; the matrix `M_-(a)` has det `1` | B1, 30 L |
| `phase_osc` | `U(-mu^2/2, mu t sqrt 2) = 2g(mu)(1-t^2)^{-1/4}[cos(mu^2 eta - pi/4) + O(mu^{-2})]`, `|t| <= 1-eps`, **all real `mu >= mu0`** | 12.10.18 | upstream `pcf_oscillatory_parameter_uniform` is unproved. For `mu^2 = 2n+1`: `U(-n-1/2, z) = e^{-z^2/4} He_n(z)` (vendored `parabolicCylinderD_nat`) `= pi^{1/4} sqrt(n!) phi_n(z/sqrt 2)` (`HermiteFunction.hermitePhi`) and `HermiteBulkMain.hermite_bulk_PR` (`|R| <= C/(n+1)`, `|x| <= (1-eps) sqrt(2n+1)`) gives the field with `2 g(mu) = pi^{1/4} sqrt(n!) sqrt(2/pi) mu^{-1/2}`. Checked at `n = 5, 30, 200`: `mu^2 |rel err| <= 0.66`. Not derivable for non-lattice `mu` without Olver's oscillatory uniform theory | **NOW on the lattice** (200 L); HARD for real `mu` (Finding 2) |
| `env_well` | `a <= 0, z >= 0`: `sqrt(u~^2 + u~'^2/k2) <= C E_well M_bal`, `sqrt(v~^2 + v~'^2/k2) <= C E_well^{-1} M_bal` | lem:cha-PCenv (1b); Olver Ch.11 Thm 3.1 | no upstream/own Lean for non-integer `a`. Our `HermiteKappaEnvelope.weber_envelope` is the crude template for integer `a` only (needs `WeberData`, an `L^2` mass) | **B2** (section 3) |
| `env_bar` | `a > 0`, all `z`: `kappa U(a,z)` and `kappa U(a,-z)` envelopes with `E_bar^{±1}` | (2) | LG recessive at `+infty` on all of `ℝ` for `a >= 1` (section 3, E4); `a in (0,1)` compact | **B2** |
| `molv_well`, `molv_bar` | `M_Olv` two-sided `~ kappa^{-1} W_well M_bal` resp. `kappa^{-1} E_bar M_bal`, all `z` | eq:cha-MolvEquiv, eq:cha-envbar | upper half = `env_*`; lower half needs lower bounds of `E_U` (E0 + E2 + `beyond`) and `E_V(|z|)` for `z < 0`, `a <= 0` | **B2** |
| `beyond` | `z >= 2 sqrt(max(-a,0))`: `|U'| <= 4 sqrt(k2) U`, `kappa |U| >= (cPC/sqrt 17) E M` | (3) | `|U'|` bound: `U` convex positive decaying, Riccati barrier `m = -U'/U <= C sqrt(k2)` (~150 L, no LG); lower bound: LG exponent (E4) | **B2** |
| `U_pos` | `U(a,z) > 0` for `z >= 2 sqrt(max(-a,0))` | 12.9.1 | `a > -1/2`: Laplace integral 12.5.1 (`parabolicCylinderU_eq_integral`, upstream `EquationAndIntegrals` 334, proof via `IsWeberSolution` and Moment lemmas, extractable, ~250 L) gives `U > 0` for all `z`. `a <= -1/2`, `z >= 2 sqrt(-a)`: `U` decays (12.5.1 + the shifts 12.8.2/3 give `O(e^{-z^2/4} poly)`), `(U^2)'' = 2U'^2 + 2 p U^2 >= 0` for `p >= 0`, so a zero at `z0 >= z_t` forces `U ≡ 0` on `[z0, infty)`, contradicting `wronsk`; positivity from sign at infinity (12.5.1 / shifts). Numerically `U > 0` on all tested `a in [-400, 0]`, `z >= z_t` | B2-light, 300 L |
| `V_growth` | `V > 0`, `V' >= cV sqrt(k2) V` for `z >= 2 sqrt(max(-a,0))` | app_thmA Step 3 (ii) | **false as stated** at `a >= 0`, small `z` (Finding 1). True with `z >= max(2 sqrt(max(-a,0)), 1)` numerically, `cV` about `0.37`; for `a <= 0` near the turning point the sign of `V` needs Airy-scale information (section 3, E6) | restate; far-region version B2-light 300 L; full version HARD |

PC-related fields of the charts (`SoftParabolicCylinder.lean`, `TransferCoefficients.lean`):

| field | content | verdict |
|---|---|---|
| `wfW_eq`, `wf2_eq`, `wf3_eq`, `W_defW`, `W1_def..W3_def`, `M_defW`, `M1_def`, `M2_def` | the chain's model pair and weights *are* `ut/vt/pcMinus/pcSwap` and `Ewell/Eminus/Eswap/Mbal` | by definition (`rfl`) when the chain is built from `U, V`; no analysis. `pcSwap_eq_pcMinus` is already proved from `reflect, reflect_V` |
| `valid`, `validW` (SM1-SM3, envelopes, `W_mono`) | for the Weber ladder `Pi_+` has entries from 12.8 (B1); the PC ladder is the exact solution-operator `Y(z+d) Y(z)^{-1}` of the fundamental matrix `[[U,V],[U',V']]`, invertible by `wronsk` (B1); `env` is `env_well/env_bar` (B2); `W_mono` is elementary from `Ewell, Ebar` | B1 + B2 |
| `ratio2`, `grow3`, `lb_pc`, `lb_weber`, `clb`, `collar_lbW` | need `V > 0`, `V' >= cV sqrt(k2) V`, `kappa |U| >= c E M` **only at rows with `z^2 - 4A >= c/h`, `A <= C/h`** (`zeta_far`, `muS_bd`, `Y_forb`), i.e. far from the turning point: there the LG error variation is `O(h^{1/2})`, small | B2-light (E4 with small error); do not need the Airy zone |
| `TransferInputs`, `TransferInputsDn` (`reg_*`, `t12_lb`, `alpha_lb`, `parity_*`) | no statement about `U, V` as such: `Pi_pm`, `AA`, `BB` of the chain; entries of `Pi_+` are explicit (z/2, `a+1/2`, `kappa(a+1)/kappa(a)`) or the fundamental-matrix quotient | B1 for the closed forms; their `C^2` bounds in `(u,X)` need `smooth_*` and the envelopes at the nodes (B2 consumption); not read further |

## 3. Proof plan for the B2 block (one "Weber envelope theorem")

Mechanism (why the constants are what they are). Put `A = -a`, `Lam = max(|a|,1)`, `p = z^2/4 + a`. For `|a| >= 1` the scaling `z = sqrt(Lam) x` turns Weber into
`y_xx = Lam^2 f(x) y`, `f = x^2/4 -+ 1`: a large-parameter problem `u = Lam` with one turning point (well) or none (barrier). The LG error-control function
`F` has variation `int |f^{-1/4}(f^{-1/4})''| ~ A^{-1/4} delta^{-3/2}` at distance `delta` from `z_t = 2 sqrt A`; it is `O(1)` exactly when `p ~ A^{1/3}`, which is **why `k2` has the
floor `max(|a|,1)^{1/3}`** (Airy scale). Normalisation is explicit at `z = 0`: `U(a,0), U'(a,0)` are Gamma quotients (12.2.6-7); with the reflection formula
`E_U(a,0)^2 = U(a,0)^2 + U'(a,0)^2/k2` has the `sin^2 + cos^2 = 1` structure (resonance-free) and equals `pi^{-1} 2^{A-1/2} Gamma(1/4+A/2)^2 (1+O(1/A))` (checked: ratio `1.0006, 1.00004, 1.0000` at `A = 10, 40, 300`); with the duplication formula this is
`kappa^{-2} M_bal^2` up to `Gamma(x+1/4)/Gamma(x+3/4) ~ x^{-1/2}`; the full envelope ratios stay in `[0.631, 1.79]` up to `a = -300`.

Steps (dependency order; "uniform" says what the constants may depend on: **absolute** unless stated; never on `a, z, h`):

* **E0 Gamma normalisation at the origin** (`a <= 0` and `a > 0`): `c <= kappa E_U(a,0) / M_bal(a,0) <= C` and the same for `E_V(a,0)` with `kappa^{-1}sqrt(pi/2)`;
  two-sided Wendel/Gautschi bound for `Gamma(x+1/4)/Gamma(x+3/4)` from log-convexity (`Real.convexOn_log_Gamma`; our `GammaRatio` is only asymptotic and non-uniform),
  reflection to remove the poles (`rgamma`), `|a|` small by compactness. ~300 L, 1 round.
* **E1 Variation estimates** (calculus, explicit): choose `z1` with `q(z1) = c0 A^{1/3}` inside the well and `z2` with `p(z2) = c0 A^{1/3}` outside (`c0` fixed so that
  `V_osc <= 1/4`); show `int_0^{z1} |q^{-1/4}(q^{-1/4})''| <= 1/4`, `int_{z2}^infty (same for p) <= C`, and for `a >= 1` the total over `ℝ` is `<= C`. ~500 L, 2 rounds. **Main technical risk**
  (explicit constants, three regimes `A >= A0` large, `A` bounded by compactness, `a >= 1`).
* **E2 Oscillatory zone `[0,z1]`** (`a <= -A0`): `exists_solution_expansion_oscillatory_finite_endpoint` (vendored, patched public; hypotheses: open order-connected `S`, `A ≠ 0`,
  `As 0 = 1`, `hrec` defining `Ad 1`; `n = 1`; error `exp(V_{0,z}) - 1`). Real `U = alpha w + conj(alpha w)` with `alpha` fixed by `(U(0), U'(0))`: `E_U(z)/E_U(0) in [c,C] A(z)/A(0)`, same for `V`. Gives `env_well` and the lower half
  of `molv_well` for `0 <= |z| <= z1` (negative `z` by `reflect`, `reflect_V`). ~400 L, 1-2 rounds.
* **E3 Airy zone `[z1, z2]`** (length `~ A^{-1/6}`): no LG. The regularised energy `R = y^2 + y'^2/k2` satisfies `|(log R)'| <= (2 + c0) sqrt(k2) + |(log k2)'|`, integral `O(1)` over the zone: both directions of the bound,
  hence `R(z2) ~ R(z1)` (constants `e^{±C}`). ~250 L, 1 round. (Alternative: Sturm comparison / Airy envelopes of `FormalResearch/Special`, `AiryBiEnvelope`, `AiryOlver` — not needed, we only ask for `O(1)`.)
* **E4 Exponential zone `[z2, infty)`**: `exists_solution_exp_of_pos` (vendored, `u = 1`, `f = p`, tail variation `<= C`) gives the recessive `w_rec = p^{-1/4} e^{-xi}(1+eps)`; `U = c w_rec` because `U` decays
  (12.5.1 + shifts, see `U_pos`) and both are recessive (Wronskian argument, as upstream `CylinderLiouvilleGreen.eq_mul_of_tendsto`, ~60 L to re-prove); `c` fixed by `R(z2)`. `E_well(z)/E_well(z2) = exp(-int sqrt p)` exactly, so
  `env_well` (U-part), `beyond`, `molv_well` for `z > z2`. `V = c1 w_dom + c2 w_rec` with `w_dom` from `exists_solution_expansion_dominant_exp_finite_endpoint` (endpoint `z2`); `c1 c = sqrt(2/pi)/(2(1+O(eps)))` from `wronsk`, `|c2 c| <= C` from E3: gives the upper
  bound for `V`'s envelope (V-part of `env_well`) and, for `z` with `int_{z2}^z sqrt p >= C'`, `V > 0` and `V'/V >= c sqrt p` (**far-region `V_growth`**). For `a >= 1`, `env_bar`, `molv_bar`: the same LG solution on all of `ℝ` (tail variation uniform in `z in ℝ`), normalised at `z = 0` by E0; the second pair member `U(a,-z)` is `w_dom`-type. ~500 L, 2 rounds.
* **E5 Assembly and compact range**: `|a| <= A0` (`A0` absolute): ratio functions are jointly continuous and positive on `[-A0,A0] x [-Z0,Z0]` (needs `smooth_*` joint continuity; `E_U > 0` since `U, U'` do not vanish together), LG tails for `|z| >= Z0` where `p >= z^2/8`;
  `a` between `-A0` and `0` and the half-integer resonances need no special case (`E_V`, `E_U` are resonance-insensitive). Produces the constants `cPC, CPC`. ~600 L, 2-3 rounds.
* **E6 Sign and growth of `V` near the turning point** (only for the *unrestricted* `V_growth` and `V > 0` on `[z_t, z2]`): crude LG constants cannot decide the sign (`c2 w_rec` and `c1 w_dom` are comparable at `z2`). Needed: the unique zero `xi_V` of `V` after the last zero of `U` lies left of `z_t`
  (numerically `xi_V` at about Airy `-1.17` against `z_t`). Route: Sturm comparison (`ODE.sturm_comparison`, `IsSol.exists_zero_Icc_of_comparison`) with the tangent-line Airy potential `L = sqrt(A)(z - z_t) <= p` (convexity, `p - L = (z/2 - sqrt A)^2`) and `Bi` envelopes; fragile. **Recommendation: do not prove; drop or restate** (Finding 1).

Alternatives considered and rejected: (i) Hermite Plancherel-Rotach for all `a` — only `a = -n-1/2`; the ladder `a -> a-1` loses constants (`z/2 - d/dz` is not norm-controlled without orthogonality); (ii) Prüfer variation with
`|d log R|` only — no cancellation, loses `A^{1/2}` in the well (needs the second-order LG error-control, which is what E2 uses); (iii) Laplace-method envelope for `a > 0` from 12.5.1 — needs Stirling with explicit constants, longer than E4;
(iv) an index-direction Jacobi-chain (`z U(a) = U(a-1) - (a+1/2) U(a+1)`, 12.8.1) through `discrete_airy_full_unif`: speculative idea row, not scoped.

## 4. Findings for the frozen structure

1. **`V_growth` is false.** For `a = 1/2`: `V(1/2, z) = sqrt(2/pi) e^{z^2/4}` (checked to `8e-51`), so `V'(1/2,0) = 0 < cV sqrt(k2) V(1/2,0)`. For `a = 3/2, 7/2` (all `a = n + 1/2`, `n` odd) `V(a,0) = 0`, so even `0 < V a z` fails at `z = 0`
   (`V(a,0)` has `1/Gamma(3/4 - a/2)^2 = 0`; `V'(a,0)` has `1/Gamma(1/4 - a/2)^2 = 0` at `a = 1/2 + 2k`). Numerically `V'/(V sqrt k2)` over `a > 0`: min `0` for `z >= 0`, `0.217` for `z >= 0.5`, `0.373` for `z >= 1`, `0.704` for `z >= 2`
   (docstring's `c_V = 0.09` was checked on `a in {-20.3,...,30}` at points that missed the resonances). For `a <= 0` (`a` down to `-400`, `z >= z_t`) the minimum is `0.429`. **Fix:** hypothesis `z >= max(2 sqrt(max(-a,0)), 1)`, or drop (unconsumed; the chart fields `grow3`, `ratio2` are used only for `z^2 - 4A >= c/h`).
2. **`phase_osc` is stronger than its use**: all consumers (`phase_pack`, `BulkPhases.lean` line 181) instantiate `mu^2 = 2n+1`. Upstream proves nothing for real `mu`. Restating the field for `mu = sqrt(2n+1)` makes it NOW (Hermite P-R, 200 L); keeping real `mu` makes it HARD (the oscillatory Olver expansion is unproved upstream and absent here).
3. **Docstring "Nothing in Mathlib defines `U, V`" is outdated**: `U, V` are defined and their Wronskian, ODE, recurrences vendored (`ThirdParty/lean-dlmf`); the `ParabolicCylinderFacts` module docstring and `PLAN.md` item 1 should say so.
4. Joint smoothness (`smooth_U/V`) is *not* upstream (only separate holomorphy). The consumers need less; see table.
5. **Constants.** Over `|a| <= 300`, all `z`: `kappa^{-1}`-normalised `M_Olv` ratio in `[0.631, 1.755]` (non-resonant) and `[0.631, 1.788]` at integers (at half-integers `a in {-0.5,-1.5,-5.5,-20.5}` the ratio only reaches `1.39`, independent review); so `cPC <= 0.631`, **`CPC >= 1.79`** (docstring: `1.74`, taken from non-resonant points). `env_well` U-part `[0.631,1.049]`, V-part `[1.0,1.585]`; barrier `a in [1e-4,200]`: `env_bar` `[0.841,1.281]`/`[0.841,1.288]`, `molv_bar` `[0.841,1.281]`.
   `beyond`: `|U'|/(sqrt(k2) U)` in `[0.492,1.161]` (well), `[0.478,1.197]` (barrier), `kappa|U|/(E M)` in `[0.420,0.887]` / `[0.556,1.023]`: `c3 = cPC/sqrt 17 <= 0.153` is consistent. `molv_well` at `z < 0` and `env_*` checked at `z/z_t in {0,...,3}` on both signs of `z`.
6. `kappaBal` jumps by `(pi/2)^{1/4}` at `a = 0` (the limit from the left is `pi^{-1/4}`, from the right `(2 pi)^{-1/4} pi^{1/4} = 2^{-1/4}`; see `PCOrigin.lean`). Harmless (`lamL_cont` already notes the cancellation) but it means `env_*` constants cannot be proved by continuity across `a = 0`; the compact piece E5 must treat `a <= 0` and `a > 0` separately.
7. No sign error or wrong constant found in `shift_*`, `reflect`, `reflect_V`, `wronsk`, `ode_*`, `env_*`, `molv_*`, `beyond`, `U_pos`, `phase_osc` (residuals `<= 4e-38` where exact; ratios in the stated ranges).

## 5. Ranked work list

| # | item | first concrete step | mandatory negative regression | size |
|---|---|---|---|---|
| 1 | **B1.0 real restriction + B1.1-B1.2 identities**: `pcU, pcV`, reality, `HasDerivAt`, then `ode_*`, `wronsk`, `shift_*`, `reflect`, `reflect_V` (9 fields) | vendor `WronskiansAndConnections.lean` (drop the `EquationAndIntegrals` import) and `ElementaryProperties.lean` lines 104-225; state `pcU_wronsk` | the sign-flipped `shift_V_dn` (`+ (a-1/2) V(a-1)`) must not be provable: prove `¬` at one witness (`a=0, z=0` from `parabolicCylinderV_zero/VDeriv_zero`); and `reflect` at `a = 1/2` is false (`pi/Gamma(1) ≠ 0 = cos(pi/2) Gamma(0)`) | 450 L, 1-2 rounds |
| 2 | `phase_osc` on the lattice (restate field) | `U(-n-1/2, sqrt2 x) = pi^{1/4} sqrt(n!) hermitePhi n x` from `parabolicCylinderD_nat`; then `hermite_bulk_PR` | the same statement with phase `+ pi/4` (instead of `- pi/4`) must fail (as `HermiteBulkMain` numerics) | 200 L, 1 round |
| 3 | `smooth_U/V` (weak form first) | joint continuity of `(a,z) ↦ u1,u2` via locally uniform convergence; then decide whether the full `ContDiff` is worth it | the classical form of `V` (`Gamma(1/2+a)/pi (...)`) is `0` at `a = -1/2` under Lean's `Gamma 0 = 0`, while `V(-1/2, 1) ≠ 0`: a `smooth_V` proof must go through the reciprocal-Gamma definition, so assert `V(-1/2,1) ≠ 0` (continuity in `a` at the pole) | 150-450 L |
| 4 | E0 Gamma normalisation | log-convex Wendel bound for `Gamma(x+1/4)/Gamma(x+3/4)` | the lower bound with `M_bal` replaced by `1` fails for large `|a|` (witness `a = -300`, `z = 0`: `kappa E_U / M_bal in [0.63,1.75]` while `M_bal = 300^{-1/4} = 0.24`) | 300 L |
| 5 | 12.5.1 extraction, `U_pos`, decay of `U` (all `a`) | extract `parabolicCylinderU_eq_integral` and its Moment lemmas from `EquationAndIntegrals.lean` | positivity must fail just below the turning point: `U(-10, z)` has its last zero at `z ~ 4.70 < z_t = 6.32`, so `0 < U a z` for `z >= 2 sqrt(-a) - 2` is false | 300 + 250 L |
| 6 | E1 variation estimates | `exists` explicit `z1, z2` and the bound `V <= 1/4`, `V <= C`; first for `a >= 1` (no turning point) | with the floor `A^{1/3}` replaced by `1` the tail variation is `~ A^{-1/4} delta^{-3/2}` at `delta = A^{-1/2}` (`p = 1`), i.e. `~ A^{1/2}`, unbounded: assert the failure of `V <= C` for `A = 10^6` | 500 L |
| 7 | E4 for `a >= 1`: `env_bar`, `molv_bar` | `exists_solution_exp_of_pos` with `f = z^2/4 + a`, `g = 0`, `a0 = -L` | the lower half of `molv_bar` with `E_bar^{-1}` in place of `E_bar` fails at `z = 5` (`U ~ E_bar << E_bar^{-1}`) | 500 L |
| 8 | E2 + E3 + E4 for `a <= -A0`: `env_well`, `molv_well`, `beyond` | E2 with `n = 1` finite-endpoint oscillatory LG; `|U'|` Riccati barrier (`beyond` part 1) | the lower bound `kappa U >= c E M` of `beyond` with `E` replaced by `1` fails at `z = 2 z_t` (`U ~ E_well << 1`) | 900 L, 3 rounds |
| 9 | E5 compact range, constants | joint continuity + positivity on `[-A0,A0] x [-Z0,Z0]`; combine to `cPC, CPC` | `CPC < 1.75` must be refuted (numerics: `1.755` non-resonant, `1.788` at integer `a`, only `1.39` at half-integers) | 600 L |
| 10 | far-region `V > 0`, `V' >= cV sqrt(k2) V` | after E4: `c1 > 0` from `wronsk` | the unrestricted `V_growth` is refuted by `V'(1/2,0) = 0` (Finding 1) | 300 L |

## 6. Verdict on the structure

* **Provable for the actual functions in the foreseeable rounds (about 4-6 rounds):** `cPC_pos`, `cPC_le` (once constants exist), `ode_*`, `wronsk`, `shift_*`, `reflect`, `reflect_V`, `smooth_*` (weak form: 1 round; full: 2), `phase_osc` on the lattice. This discharges every field that the pipeline's Lean proofs consume except the envelope block.
* **Provable but a project of its own (8-12 rounds, ~4-6k L, risk concentrated in E1/E5):** `env_well`, `env_bar`, `molv_*`, `beyond`, `U_pos`, far-region `V` facts. Everything except the Airy-zone bookkeeping uses the vendored LG theorems directly.
* **Should remain Prop-level hypotheses (or be restated):** the unrestricted `V_growth` (false), real-`mu` `phase_osc`.
* **Recommended refactor (no field renamed, no consumer touched):** split into `PCExactFacts U V` (11 B1 fields + `smooth`), `PCEnvelopeFacts U V cPC CPC` (`env_well`, `env_bar`, `molv_*`, `beyond`, `U_pos`) and `PCPhaseFact U`; define `ParabolicCylinderFacts := PCExactFacts + PCEnvelopeFacts + PCPhaseFact + cPC_pos + cPC_le`.
  Then the pipeline headlines (`propThaW2_proved`, `thmA_of_layer4`, ...) can be restated with `PCEnvelopeFacts U V cPC CPC` as the **only** remaining special-function premise, a single Prop with an explicit mathematical statement (Olver Ch.11 Thm 3.1 for Weber), and `pcU, pcV` are the actual functions. Do not edit the frozen structure before the owner agrees; the deletions of `V_growth`, `ode_V`, `shift_*`, `U_pos`, `beyond` (unconsumed) can ride on the same decision.
* Constants for the final instance: `cPC = 0.6`, `CPC = 2` would suffice per the numerics, but the Lean statement is existential (`∃ cPC CPC`), so only positivity of the compact-range infima and the LG constants of E1 enter.
