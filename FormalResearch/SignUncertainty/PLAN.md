# Paper I (Fourier sign uncertainty, Cohn-Elkies) - Lean plan

Source: QIprojects `CFT/sign_uncertainty/paper/` (`sign_uncertainty_core.tex`, the supplement parts) and the three
`CFT/common/` files it `\input`s (`airy_poisson.tex`, `clark_airy.tex`, `two_edge_bootstrap.tex`), read at QIprojects
`origin/main` `2587d989b` (2026-11-25; result counts and line references in this file re-checked at that commit). Lean state: reasoner `master` as in section 3 (the Lean state is kept in the tables, not here). Reader-facing status:
QIprojects `docs/lean_status.md` (section "Paper I sign uncertainty"). This file says what is true now; history is in git.
Wording: "proved" means a Lean theorem on `master` with the declaration named; "stated" means a Lean `def`/`Prop` or a
hypothesis structure with no proof; "proved modulo fields X" means a theorem whose hypothesis structure has the open
fields X. A `.lean` file existing is not verification.

## 1. Where we are

| fact | state |
|---|---|
| size | `SignUncertainty/` 237 files, 63.7k lines; `CohnElkies/` 65 files, 53.6k lines; `Special/Airy*` about 48k lines; `TwoEdgeBootstrap/` 4k; `Asymptotics/` 3k |
| placeholders | no proof placeholder and no declared `axiom` anywhere in `FormalResearch/` (grep). The headline theorems in `Headlines.lean` are guarded by `#guard_msgs` to `[propext, Classical.choice, Quot.sound]` |
| last recorded full build | `lake build FormalResearch.SignUncertainty FormalResearch.TwoEdgeBootstrap`, 9,269 jobs, about 9 min (audit of 2026-11-23; not re-run for this documentation pass) |
| paper headlines | three introduction theorems: `thm:intro-radii` (five-term radii), `thm:intro-hb` (bounded remainder at every fixed level), `thm:intro-gap` (CE thresholds at prescribed shells) |
| unconditional headline in Lean | none |

### 1.1 Headline status: paper statement against Lean statement

| paper | Lean (`Headlines.lean`) | matches the paper? | open inputs |
|---|---|---|---|
| `thm:intro-radii`, alias of `thm:ct-upper` (`general_theorems.tex`), for real `c >= c_0` (non-effective): (i) `Delta_5^eps(c) - C c^{-1} log c <= T_c^eps <= Delta_5^eps(c) + C c^{-3/4}` (`eq:ct-lower`), with `Delta_5^eps = c/pi^2 + A c^{1/3} + kappa_eps + c_1^Langer c^{-1/3} + d_2^{*,eps} c^{-2/3}`, hence `T_c^{+1} - T_c^{-1} = -1/pi + pi A c^{-2/3} + O(c^{-3/4})` (`eq:ct-split`); the same two-sided bound at `eps = -1` for the real-`c` Hankel Cohn-Elkies threshold `T_c^CE` (inf of `T` over mutual Hankel transforms `h, g` with `h(0) = g(0) > 0`, `g >= 0` and `h <= 0` on `[T, inf)`; `fourier_mellin.tex`, since QIprojects PR 295), so `0 <= T_c^CE - T_c^- = O(c^{-3/4})`; (ii) integer `d >= 2 c_0`, `c = d/2`: the same bound for `A_sign^eps(d)^2/2` and, as `T_c^CE = r_CE(d)^2/2`, for `r_CE(d)^2/2` (`eq:ct-two-sided-d`), so `0 <= r_CE(d)^2 - A_sign^-(d)^2 = O(d^{-3/4})`; (iii) every `d >= 2`: Airy order with `O(1)` remainder. The introduction prose adds the density formulas of `gt:7.12a` (`ce_radius.tex`: `eq:ce-density-exact`, `eq:ce-density-ratios`, `eq:ce-radius-differences`, `eq:ce-log-density`), which are not part of `thm:ct-upper` | `thm_intro_radii`, `_sign`, `_ce`: the `O(1)` Airy-order law for `A_sign^+-(d)`, `r_CE(d)` for all `d >= 2` and the volume bound up to constants and `O(1)` in the log | **No: weaker.** It has the shape of `thm:ct-upper` (iii) and `gt:7.12a` only; the five-term statements `eq:ct-lower`, `eq:ct-two-sided-d`, `eq:ce-density-exact` are not stated | `RadiiInputs`: `ce_hb_lift_m1` (= `CeHbLift ShellHBData.airy`, proved from the open `CeHankelPair`). Its other field `hb_thresholds_upper` is the theorem `hbThresholdsUpper` (`HbUpperM1`), kept as a field only because `HbUpperM1` imports `Headlines` (housekeeping, S: move the radii headline below `HbUpperM1` and drop the field); `hb_thresholds_lower` is a theorem |
| `thm:intro-hb`, alias of `u1cl:multilevel` (`u1c_o1_lower.tex`): fix real `P, Q` with `Q + iP` a nonzero constant or with all zeros in the open lower half-plane (`eq:hb-profile`, `clark_airy.tex`), `N = P Ai + Q Ai'`, `m = max(2 deg P + 1, 2 deg Q + 2)`, `R_off >= 0`. For either eigenvalue, large real `c` and levels `T_{j,c} = c/pi^2 - (t_j/beta_1) c^{1/3} + r_{j,c}`, `|r_{j,c}| <= R_off`, `1 <= j < m`, the infimum `T_{m,c}^{opt,eps}` over feasible `f in A_c^eps` with `f(T_{j,c}) >= 0` equals `c/pi^2 - (t_m/beta_1) c^{1/3} + O_{P,Q,R_off}(1)` (`eq:hankel-hb-bound`); it is attained and unchanged by the extra condition `f(0) = 0` (via `gt:7.9a`, `gt:7.9b`); the constants are uniform in the offsets | not stated | - | one-level halves exist (`HbThresholdsLower`, `HbThresholdsUpper`); all-level `(P,Q)` is M8 |
| `thm:intro-gap`, alias of `thm:ce-canonical-iff` (`ce_canonical_iff.tex`), for the same `(P,Q)`, `G_N = N^2/prod_j (t_j - u)`, `L_y(F) = e^{-y^3/12} int F e^{yu} du`: (1) `u_LP <= t_m`, with equality iff `L_y(-G_N) >= 0` for all `y > 0`; for `m >= 2`, `Lambda_M <= lambda < u_sh <= u_LP` (`M >= m`), `Lambda_m > a_m`, `lambda >= tau_N > t_{m+e}`; if `u_LP < t_m` every optimizer has a positive Laplace zero of even order, and `eq:airy-deflation-obstruction` holds; (2) `u_sh = u_LP` under the integral criterion (a) or the node-sign criterion (b), in particular whenever `u_LP >= t_{m+2}` and for every configuration with `m <= 5`; (3) the equivalence of (i) `L_y(-G_N) >= 0` for all `y > 0`, (ii) `(R_d^CE)^2/2 = d/(2 pi^2) - (t_m/beta_1)(d/2)^{1/3} + O(1)` for every offset bound `R_off` (`eq:ce-canonical-iff`), (iii) `lim rho_d = -t_m/beta_1` for all shells with offsets `o(c^{1/3})`, (iv) `liminf rho_d = -t_m/beta_1` for some such shells (for instance offsets `0`); failure of (i) forces a strict Airy-order gap (`thm:ce-shell-gap`, `eq:strict-gap`) | `thm_intro_gap_i`, `_ii`, `_ii_even`, `_iii` for a configuration `D : ShellHBData` | old split below: (i) yes; (ii) partial: the offsets are as in the paper, but the `v = t_m` endpoint clause of `thm:ce-shell-gap` (limits `Psi/M -> G_N/||G_N||_1`, `M[hhat_c]/M[f_c] -> 0`, `L_y(-G_N) >= 0`) and the origin floor are not stated; (iii) only for strict Laplace positivity (`0 < airyLaplace (-G) y`), the paper allows weak positivity with tangencies; **(iv) not stated** | `ShellGapInputs D`: `shell_reduction`, `ce_hb_lift`. (ii) and (ii)-even do not use them (`ShellGapInputs.shell_gap_limit` ignores its argument), so they are proved; the argument is a leftover |
| none (deleted from the paper) | retired, not a headline: `separation_neg_two_div_pi_sq` (`SignSeparationLimsup.lean`, formerly `thm_intro_separation` in `Headlines`): `limsup (T_c^{+1}-T_c^{-1}) <= -2/pi^2` | superseded by `eq:ct-split` (section 5) | none: `separation_neg_two_div_pi_sq_unconditional` (from `separationInputs_holds := ⟨hbThresholdsUpper⟩`) |

Since QIprojects PR 287 the paper's introduction is prose and the three headline labels are aliases: `thm:intro-radii` on `thm:ct-upper`, `thm:intro-hb` on `u1cl:multilevel`, `thm:intro-gap` on `thm:ce-canonical-iff`. This plan keeps the old four-part split of `thm:intro-gap`: (i) `thm:ce-shell-reduction`, (ii) `thm:ce-shell-gap`, (iii) `thm:ce-canonical-iff` with `thm:ce-hb-lift`, (iv) `thm:ce-airy-transfer` with `thm:ce-canonical-iff` (2). The introduction also now states strict `T_c^{+1} < T_c^{-1}`, attainment with zero origin and precompactness at every real `c > 1/2` (`gt:7.9a` (3), `gt:7.9b`), and finite-dimensional CE attainment (`prop:ce-finite-attainment`); these are tier 2 (section 2).

Open inputs, counted once: `ce_hb_lift_m1` (M6), `shell_reduction` for `m >= 2` (M8), `ce_hb_lift` for `m >= 2` (M8).

### 1.2 What is closed and reusable

- The Airy base (A1, A2): Theorems D, Q, B with their equality cases, Clark and Hermite-Biehler quadrature, `hb_uniqueness`, Airy PWS (a)<=>(b).
- The Hankel layer (B1, B2): the concrete real-order Bessel kernel (`hankelKernelData`, unconditional), `gt:7.4`, `radial_compactness`, the Euclid-Hankel dictionary in every integer `d >= 2` (`hankel_euclid_dictionary`), `gt:7.9a` in its non-strict form `T_c^{+1} <= T_c^{-1}`, `gt:7.9b` under `T_c^{-1} > c/(4 pi)` (true at large `c`, which is all `thm:ct-upper` needs).
- The one-level Hankel thresholds (C2, C3, B3): `hb_thresholds_lower` (`HankelThresholds`; via the Langer chart, transport, band reduction, window lemma and `hankelBootHB`) and `hbThresholdsUpper` (`HbUpperM1`, from `o6Bricks_holds`, `gt1BasisInput` and `o4QuotientBound`: the analytic estimate on `|θ| = 1/4`).
- Shell extraction and the one-profile problem (E1): `hankelShellGapLimit_proved`, `shellGapLimit_of_hankel`, `one_profile_*`, `even_m_laplace_sign`, `shell_reduction_airy`.
- Cohn-Elkies radius layer (D2): `ce_quadratic_dimensions` (finite dimensions), `ce_schwartz_radius_eq_L1_radius`.
- M6 leaves (D1): the convolution source `ConvSource*` (`convS_bounds`, `ConvTailData`), `ceLift_pair`, `ceHankelPair_of_eigenfns`, `ceLift_tune`, `ceLift_physical` (proved; unconditional as `ceLift_physical_unconditional`, with `CeSourceFamily` proved for `S_c` in `ConvSourceFamily`), `ce_hb_lift_airy_of_hankelPair` (proved modulo `CeHankelPair`), `preEdge_general_pos` (modulo `PreEdgeGeneralData`).

### 1.3a Known risks in the TeX proofs and unchecked shortcut ideas (independent review of 2026-11-25, partly verified)

- **Not Lean-formalisable as stated, or black-boxed in the TeX:** `ct:cfu` cites the Chester-Friedman-Ursell theorem (the scalar cubic chart `fct:comp-cfu` / `fct:cfu-div` of `constant_terms_five.tex` builds the same chart from a divided-difference equation, so formalise that once for both); `ct:dyadic` uses DLMF 9.7.5, 9.7.6, 9.7.9 (second-order uniform complex Airy asymptotics on the upper semicircle: check `Special/AiryCft*` before staffing F1); `ct:boas` Step 1 uses Weber's identity DLMF 10.22.52 (analytic continuation in `b` of the Gaussian identity `gt:7.9a` is a candidate derivation). `fct:warp-asymp` (3)-(4) uses 44- and 60-fold integrations by parts with `C^60` symbol bounds; the review suggests that 5 (outer zone) and 5-21 (far band, shoulder) suffice with other choices of the cutoff `r`: unchecked, verify before use. `fct:warp-asymp` (3) and `fct:ce-band` run the same two-regime argument (regulator `0` or `1/c`): formalise one lemma. `fct:ce-band` applies the maximum principle to `g_D''` citing `fct:comp-D` (1), which is stated for `g_D`, `g_D'` only.
- **Computer-assisted input:** `cor:ce-rayleigh-bound` (3) (M9, `ce_two_level.tex`) rests on a 300-bit ball-arithmetic enclosure of the Neumann shell value; it is not needed for `thm:intro-gap` (i)-(iv) and is tier 2. Decimal constants of `thm:ct-upper` (`I_0`, `kappa_±`) are numerical; Lean formalises the closed forms only.
- **Paper changes on main since 2026-11-25 (standalone review fixes; no stated result a Lean row depends on is weakened):** `fct:F-def` is defined on `Re ζ ∈ [1/4, 7/16]` (`[1/8, 7/8]` for `H_CE`, `ε = -1`), not up to `1/2`; `ft:C1` holds for `c ≥ c_1`; `teb:mellin` MS3 now states both global stationary-point bounds explicitly (the Hankel instance already proves them); `ap:lemU` principal root on the open half-plane; `ct:sec4` states why the feasible `ũ₁` is a violator (`κ_± < 0`); `ct:boas` Step 5 and `ct:dyadic` (half-disc Poisson kernel bounds, Lipschitz estimate) are rewritten with explicit constants; `fct:comp-cfu`, `FCT.5`(1), `fct:psi-real` and the new `fct:inner-symbols` (FCT.5b) are F2a items. The Laguerre-LP numerics of Remark `CT.10` are corrected and its sharpness claim removed (not formalised).
- **Removed from the paper (2026-11-25, after the usage audit):** `uct:bump-est` and the unlabelled corollary "Density with a simple first zero" are deleted. Items (3)-(4) of `uct:seed-asymp` are kept (item (3) carries the error behind the remark `uct:quintic-barrier` and is checked by `verify_constant_terms_upper.py`) but `fct:warp-asymp` no longer cites them: formalise only items (1)-(2). `prop:airy-secular` and `lem:ce-rayleigh-two-level` are not needed by `thm:ce-airy-transfer`. Proof simplifications of the same pass: `fct:warp-asymp` (3)-(4) needs 5, 21 and 7 integrations by parts (not 44 and 60), through the new shared Lemma `fct:edge-ibp` (Abel-sense edge-cutoff removal and shoulder IBP, uniform in the regulator `lambda in {0, 1/c}`; also used by `fct:ce-band`); `ct:cfu` is now built from the scalar divided-difference equation by the holomorphic implicit function theorem (no black-box CFU theorem; `fct:comp-cfu` still needs its own weighted `C^14` chart); `ct:boas` Step 1 is the analytic continuation in `b` of the Gaussian identity of `gt:7.9a` (no DLMF 10.22.52); `fct:bump-sym-check` is a lemma; `ct:phase-far` is the lemma `ct:phase-far-lem`.
- **Open prerequisites cited by F1, F2a and F2b beyond the package rows:** `gt:7.7p` (d) (cited ten times by `constant_terms_lower.tex`; it invokes `teb:quant_c1` at `alpha = 0`), the weighted-Mellin clause of `u1cl:rep`, `teb:kernel` (a), `fct:bump-sym-check` (a remark with content, cited four times: `fct:physical-positive`, the proof of `fct:main-hankel`, `fct:ce-band` twice; section 6.3), `ct:phase-far` (inside the remark `ct:rem-lattices`, cited by `ct:boas`), and `eq:ce-log-density` of `gt:7.12a`, which cites `gt:7.10` (deferred). `u1cl:multilevel` (Tier 1) asserts attainment and `f(0) = 0` through `gt:7.9a`, `gt:7.9b`, whose finite-`c` compactness (`lem:finite-hankel-compactness`) is Tier 2: either move it up or state the Tier-1 target without them.
- **Owned by this plan (package G, M8):** `ft:L1`, `ft:L2`, `ft:riesz` and `fto1:mellin` are results of Paper I's Theorem FT. The Paper II plan (`ModularBootstrap/PLAN.md`, section 3.1) marks `FT-3..6` beyond `FT-CC` not planned because they are useful only for Paper I instances, and has no `FT-7`; so they are planned here, staffed with M8 (`u1cl:multilevel` at all levels), with the Lean code in `ModularBootstrap/FoldTip/` next to the existing FT files or in `SignUncertainty/` (the same code layout as the rest of FT; no change to Paper II's plan is needed). `fto1:thm` and `fto1:mellin` are invoked by the proof of the lower half of `u1cl:multilevel` (`u1c_o1_lower.tex`, lines 24-54), hence by `thm:intro-hb`; `ft:L1`, `ft:L2`, `ft:riesz` are used in the proof of Theorem FT (`fold_tip_universality.tex`).
- **Usage audit (2026-11-25; a script over the 34 Paper I files and the 3 `CFT/common/` files, citations classified by statement, proof, remark, `\internal`, prose; mentions such as "used in" or "finite version of" excluded).** Of 185 results and remarks, 18 are dead (no live citation, none from Paper II): the unlabelled corollary "Density with a simple first zero" (`ce_airy_lp_proofs.tex:742`), `fto1:sub`, `cor:ce-projection-mass` (kept as an appendix), and 15 remarks (`rem:ce-dirichlet-gap`, `rem:ce-nonhb-gap`, `rem:airy-even-deep-gap`, `thm:ce-neumann`, `fct:rem-mech`, `ct:rem-split`, `ceo:O11ak.rem`, `u1cl:rem`, `ap:remQ1`, `ap:remB1`, `ap:remB2`, `gt:remOp`, `gt:remKernel`, ...). Demoted in the rows of 6.2: `uct:bump-est`, items (3)-(4) of `uct:seed-asymp`, `prop:airy-secular`, `lem:ce-rayleigh-two-level` and `cor:ce-rayleigh-bound` (tier 2: advertised in the abstract, no theorem cites them), `cor:ce-schwartz-shells`; `ap:E4`, `ap:corQp` are done but dead. Not dead, but headline-adjacent leaves with no citing proof: `gt:7.12a`, `thm:ce-odd-family`, `prop:ce-finite-attainment`. `fct:bump-sym-check` is a remark with four proof uses (promote to a lemma, planned with F2a); the display `ct:phase-far` (`ct:rem-lattices`) is used by `ct:boas`. Closure sizes: 34 results serve only `thm:intro-radii`, 33 only `thm:intro-gap` (`thm:ce-hb-lift`, `lem:ce-lift-assembly`, `thm:ce-post-edge`, `ceo:conv`, `cepf:*`, `cegt:GT2b`, `thm:ce-shifted-lift`, `lem:ce-dual-line`, `thm:ce-laplace-zeros`), and the radii route reaches the CE lift only through the one-line identity `cepe:PE3` and the forward mention `cel:L3a` -> `thm:ce-hb-lift`. Paper II uses only Airy, Clark, two-edge and fold-tip material of Paper I (`ap:*`, `gt:1.*`, `lam:thmB`, `lem:hb-uniqueness`, `teb:*`, `ft:*`), no Hankel, constant-term or CE result. The Paper I lemma `ceo:O11ak` is live for all three headlines (see C1).

### 1.3 Recorded caveats

- Hypothesis packages of the superseded coherent-square route (Route I: `GT4CoverageBands`, `MovingDiagFarTail`, `MacroscopicTransferPackage`, the `Cardinal*`, `ClosedResolvent`, `ResolventAverage`, `MovingDiagonalSource` files, and the `hNicholson`, `hBesselRatio` fields in `CardinalSymbolBounds`) are no longer cited by the paper (Route I left the paper for `CFT/sign_uncertainty/notes/`). Per the old audit (2026-11-23, not repeated) they have only toy witnesses. Whether `M10` reuses any of them (`ceo:O11n.7`, `ceo:gauss.2` are cited by `constant_terms_upper.tex`; `AiryGaussianTransform` serves them) must be checked before anything is archived.
- `ce_radius_airy_order_of_bounds` (`CohnElkiesRadius`) is only a gluing step: its hypotheses `hlo`, `hhi` are the two halves.
- Differences from the TeX that later steps do not need: the tail exponent of `gt:7.7p` is `c/40000` in Lean and `2e-3 c` in the TeX; `(e5)` is proved for `c >= 32768` (TeX `c >= 200`); the deep-lobe bound of `radial_compactness` uses `g(sigma) < 4/3 sigma^2`; the middle band cuts in `tau`, not `theta`; `hankel_band_reduction` uses `b = 1/100` (paper `0.012880`) and is non-vacuous for `eps = -1` only; `hb_thresholds_lower` has non-sharp constants and `c_0 >= 10^14`.
- Statement gaps recorded rather than closed: `(e4)` identification `gamma_0 = c_s^{1/2} 2^{2/3} pi^{-1/2} beta_inf`; the `L >= L_0` claim of `O.3(2)`; `O.11ak` in fixed-`c` `L^1`-kernel form; `7.7p (d)` cut-crossing constant and two-level `C^1` stability; Theorem H.14 origin-floor clause and the endpoint case `u_* = t_m`.

## 2. Priority order: the headline theorems first

**Rule (owner, 2026-11-25): work goes to the paper's headline theorems first; anything not on a headline path waits.** Priority:
1. **Tier 1, `thm:intro-radii` (five terms), the main result:** M11 -> B3 -> C1 -> F1 -> F2a -> F2b -> F3 -> density (2.1). This is M10 and now the main lane.
2. **Tier 1, the other two headlines:** `thm:intro-gap` (2.3), whose (i)-(iii) reuse M6 and M8, and `thm:intro-hb` (2.2, M8).
3. **Tier 2, after the headline paths:** M6's `CeHankelPair` packaging beyond what F2a, F2b and `thm:intro-gap` (iii) use (it only completes the interim `O(1)` Lean headline); the every-`c` strengthenings of PR 287 (`gt:7.9a` (3) strict with attainment, `gt:7.9b` without the `T_c^{-1} > c/(4 pi)` hypothesis, via `lem:finite-hankel-compactness` and the reciprocal-scale Gaussian correction; `prop:ce-finite-attainment`; S-M in total); housekeeping (restating `thm_intro_gap_ii`, dropping the import-order field `hb_thresholds_upper` from `RadiiInputs`, origin-floor and endpoint clauses); constant-sharpening of proved leaves; remarks; Route I leaves.

Package ids are from section 6.1, milestones from section 3. Nothing in this section is formalised unless section 6 says so.

**The Lean headline is not the paper headline.** `thm:intro-radii` is the five-term theorem `thm:ct-upper` (i)-(ii) plus the density corollary. Its proof (`constant_terms_lower.tex`, `constant_terms_upper.tex`, `constant_terms_five.tex`) does not cite `thm:ce-hb-lift` or `thm:ce-post-edge`; the five-term CE radius is built directly (`fct:main-ce`, `fct:ce-band`, `fct:ce-preedge`; package F2b). The route-II leaves it does cite (checked against the TeX, independent review of 2026-11-25) are few: `ceo:gauss.2` and `ceo:O11n.7` (both inside `ceo:gauss`, used by `uct:airy-trans`), `cel:L3a` (1)-(2) and the first-order `cel:total-saddle` (the interface of `uct:gen-preedge`, with `cel:L5`), and the one-line Mellin identity of `cepe:PE3` (inside `cepe:general`). `constant_terms_*.tex` never cites `ceo:conv`, `cepe:general`, `cel:total-saddle-2`, and `ceo:O11ak` in a framing sentence (line 62) and in the proof of `uct:pos-floor` (line 221: the value `W_pos(c^{1/3})` follows from `ceo:O11ak` and `u1c:U2` (2)). So **M6's lift (`CeHankelPair`, `ConvSource*`, `PreEdgeCriterion`, post-edge, packaging) are not on the path of the paper's `thm:intro-radii` (general-seed `ceo:O11ak` is not either, but the one-level form is used by `uct:pos-floor`); the D1 leaves it needs are `ceo:gauss.2` (F2a and F2b, through `uct:airy-trans`) and, for F2b only, `cel:L3a` (1)-(2) in the single-strip Dini form and the first-order `cel:total-saddle`**. It completes the interim Lean headline `thm_intro_radii` (the `O(1)` law) and is the `m_0 = 1` case of `thm:ce-hb-lift`, which `thm:intro-gap` (iii) needs. `thm:ct-upper` (iii) itself follows from (ii) and `thm:ce-gaussian` (finite dimensions), as the TeX proof says.

### 2.1 `thm:intro-radii` (five terms): M11 -> B3 -> C1 -> F1 -> F2a -> F2b -> F3 -> density

1. **M11**, `u1cl:main`: done at one level (`hankel_one_two`). Used by `constant_terms_lower`.
2. **B3**: `u1cl:langer` done (`u1cl_langer`); the clauses of `gt:7.7p` (d) that the lower bound cites (cut-crossing constant; `gt:7.7p` is cited ten times in `constant_terms_lower`).
3. **C1**: `uct:admiss` (Lemma T.8; done, with `mat:T7`); `constant_terms_upper` cites it seven times and `constant_terms_five` four times. `ceo:O11ak` is used by `uct:pos-floor` (radii), by `u1c:U3` (membership of the lift, `thm:intro-hb`), by `uct:admiss` ("as in") and `cel:L3a`, and by the gap lift; Lean has it for the one-level seeds (`exists_hankelEigenfn_lift`, `m >= 3`; check that `S_pos = g_1 + g_1' - f_1/4` at `m = 4` is in that family) and, for general seeds, modulo `ConvTailData` (proved for `S_c`).
4. **F1** (XL): `ct:outer` first (it is also the input of F2a and F2b), then `ct:dual-id`, `ct:cfu`, `ct:morse-expansion` (finite real stationary phase), `ct:boas`, `ct:dyadic`; `ct:boas` is now proved from the finite Fejér inequality `ct:fejer` (only `g in L^1` needed), not pointwise Poisson periodization, so no Poisson summation formula is required; `ct:dyadic` closes by absorption at a fixed dyadic depth; gives the five-term lower bound and the lower half of `eq:ct-split`. Inputs already in Lean: `mat:T1`, `mat:T4`, `gt:7.7b`, `gt:7.7c`, `radial_compactness`, `airy_defect_bound`, `hb_thresholds_lower`.
5. **F2a** (XL, 19 results, 1,648 TeX lines): the Hankel upper bound `fct:main-hankel` and the lemma chain that F2b reuses. The `uct:*` lemmas (`airy-trans`, `pos-floor`, `strip-split`, `bump-symbol`, `bump-weighted`, `seed-asymp` items (1)-(2); `bump-est` is deleted from the paper), then the `fct:*` chain (`moment-solver`, `comp-D`, `comp-cfu`, `phikill`, `warp-asymp`, `splitting`, `bump-5`, `cusp-edge`, `unscaled-cusp`, `physical-budget`, `physical-positive`) to `fct:main-hankel`. **F2b** (XL, 6 results, 477 TeX lines, on top of F2a): the CE radius `fct:main-ce` with `fct:ce-band` and `fct:ce-preedge`, and the three lemmas only they cite: `uct:ce-band`, `uct:gen-preedge`, `uct:outer-growth`. Since QIprojects PR 295 the target of F2b is the real-`c` Hankel threshold `T_c^CE` (mutual Hankel transform pairs, no integrality of `2c`), so F2b should be stated on Hankel pairs at real `c` with no Euclidean input; the passage to `r_CE(d)` for integer `d` happens once, in F3. There is no shared-lemma package F2s: every F2a lemma except `uct:bump-est` is cited by `fct:ce-band`, `fct:ce-preedge` or `fct:main-ce`, directly or through `fct:comp-D`, `fct:warp-asymp`, `fct:bump-5` (`fct:moment-solver`, `fct:comp-cfu`, `fct:phikill`, `uct:seed-asymp`, `uct:bump-symbol`, `uct:bump-weighted` are reached through those), and the CE proofs cite the construction and estimates of `fct:main-hankel` (`fct:ce-band`: the theorem and the regime table `fct:tab-regimes`; `fct:ce-preedge`: the theorem; the proof prelude of `fct:main-ce`: `fct:hg1-win`, `fct:hg1-mac`), so the shared base is F2a itself, finished before F2b. Inputs already in Lean: `u1co:O3`-`O5` at one level, `airySquare_gaussian_transform`, `lobe_saddle_asymptotic`, `cel:L3a`/`L4`/`L7`, `mat:T1`-`T4`. D1 leaves: F2a needs only `ceo:gauss.2`; F2b needs `cel:L3a` in its single-strip-multiplier form (Dini modulus at the origin) (extends the Lean `OriginMellinAndS0`, M) and `cel:L5` in its first-order total-multiplier form (`cel:total-saddle`, used by `uct:gen-preedge`; done: `lobe_total_saddle`; `cel:total-saddle-2` is not cited). **Formalisation shape (PR 287):** one shared lemma per mechanism, instantiated twice: the bump symbol class `uct:bump-symbol`/`uct:bump-weighted` at both cutoff scales (replaces degree-21 coefficient bookkeeping), `fct:cusp-edge` for every reflected cusp term, `fct:moment-solver` for any fixed number of moments, the scalar cubic chart `fct:comp-cfu` (no function-space implicit-function theorem), and the four-band criterion `fct:physical-budget`/`fct:physical-positive` for both the Hankel and the CE construction. The CE Fourier edge keeps its own regularized Airy-square calculation.
6. **F3** (S): `thm:ct-upper` (i), (ii) with the reductions `hankel_euclid_dictionary`, `intertwiner_feasible`, `ce_schwartz_radius_eq_L1_radius`, `hankelT0_eq_hankelT`; (iii) from (ii) and `ce_quadratic_dimensions` (or from the Lean `thm_intro_radii` once M6 closes).
7. **D2**: `gt:7.12a` exact density `eq:ce-density-exact` (S), then `thm:intro-radii` (S).

Steps 1 to 3 are independent. F2a needs from F1 `ct:outer` (the outer function `G_eps` and its phase, cited 15 times in `constant_terms_upper.tex` and `constant_terms_five.tex`), `ct:cfu`, `ct:dual-id` (1), `ct:morse-expansion` and the Langer chart inversion `ct:langer-inv` (an equation of the CFU discussion before `ct:morse-expansion`, not a result label); F2b needs `ct:outer` and `ct:dual-id` (1); `ct:boas`, `ct:dyadic` are lower-bound only, and the upper bounds cite `thm:ct-lower` only to combine into two-sided statements. So F1's first block (`ct:outer`, `ct:dual-id`, `ct:cfu`) comes first, then the two bounds proceed in parallel (F2b after F2a). The sign-radii half of (ii) needs F1 and F2a (`fct:main-hankel`) only; the CE half needs F2b (`fct:main-ce`).

### 2.2 `thm:intro-hb`: A3 + B3 + C2 (all levels) -> C3 (M8)

1. **A3**: `TE.0'` for polynomial `(P,Q)` as a converter into `ChartCompactness` plus the shared rigidity theorem (agreement with the FoldTip lane, section 5); Hankel `BootstrapHBInstance` at every level.
2. **B3**: `u1cl:langer` is done; what remains for all levels is `gt:7.7p` (d) and the weighted-Mellin clause of `u1cl:rep`.
3. **C2** (L): `U.2`, `U.3`, `GT.1`, `O.3`-`O.6` for the rational-Airy seeds of a general `(P,Q)`; `lem:hb-seed-mass` and a witness `HBSeedSpec` at every level.
4. **B1**: `gt:7.5` for general `(P,Q)`.
5. **C3**: `u1cl:multilevel` (both halves, with the `f(0) = 0` clause; its TeX proof of the lower half invokes `fto1:thm` and `fto1:mellin`, the latter is planned here with M8, section 1.3a); then `thm:intro-hb` (S).

### 2.3 `thm:intro-gap`

- (ii): partial: the Lean statement is proved, without the origin-floor clause and the `u_* = t_m` endpoint clause (`thm:ce-physical-profile`, `thm:ce-shell-gap`). Housekeeping (S): restate without the unused `ShellGapInputs` argument and add the two clauses.
- (i): `ShellReduction D` for `m >= 2` (E1, M): needs `u1cl:multilevel` lower half (section 2.2) and the radial projection already in `CEShellReduction`.
- (iii): M6 (D1), then `thm:ce-hb-lift` at every level with weak Laplace positivity and tangencies (M8), `thm:ce-canonical-iff` (E2) and the Laplace-positive odd families of `thm:ce-odd-family` (E1).
- (iv): E2 (M9: `thm:airy-square-attained`, `thm:ce-airy-transfer`, `thm:ce-canonical-iff`, `rem:airy-even-deep-gap`), `cor:ce-schwartz-shells` (D2) and `thm:ce-shifted-lift` (route-II machinery at shifted nodes). E2's Airy-LP core (`thm:airy-square-attained`, `thm:ce-canonical-iff`, `thm:ce-airy-transfer`) needs only M3 and can start now; `thm:ce-shifted-lift` needs D1 (`thm:ce-post-edge`, `cepe:general`, `ceo:conv`, `lem:ce-dual-line`, `lem:ce-lift-assembly`), C1 (`ceo:O11ak`) and C2 (`u1c:U1`, `U2`, `u1co:O5`, `O6`), so it comes after M6.

### 2.4 Next concrete packages (headline paths only)

1. **Start now (tier 1, `thm:intro-radii`):** (`u1cl:langer` done; `uct:admiss` (1), (2) done) the F2a/F2b leaves from D1 (C1's `mat:T7`, `uct:admiss` and `mat:T3` are done): `ceo:gauss.2` (F2a and F2b), and for F2b only `cel:L3a` (1)-(2) (single-strip Dini form) and the B3 leaves F1 cites (`gt:7.7p` (d), the weighted-Mellin clause of `u1cl:rep`). `ceo:O11ak` is needed in the one-level form (done) by `uct:pos-floor`; its general-seed form only by the gap lift.
2. **Then:** F1's first block, `ct:outer` (done) and `ct:dual-id` ((1) done; (2) open) (`constant_terms_lower.tex`), on proved inputs only (`mat:T1`, `mat:T4`, `gt:7.7b`); `ct:outer` unblocks F2a and F2b.
3. **Continue, scoped to what the headlines use** (these serve `thm:intro-gap` (iii), not `thm:intro-radii`): M6 step (b) (`thm:ce-post-edge`; the S-side pre-edge ratio bounds need `ceo:gauss.2`, no Lean statement yet) and (c) (the `ConvSource*` symbol bounds and pre-edge estimates; no F2 result cites `ceo:conv`), and the `m_0 = 1` lift that `thm:intro-gap` (iii) needs.
4. **Second headline lane once two slots are free:** `thm:intro-gap` (iv) through M9 (E2), beginning with `thm:airy-square-attained` (needs only proved inputs: `airyNC_quadrature`, `airyAiC_logDeriv_mittagLeffler`).

**Stop conditions (tier 1).**
- **C1:** reached for `thm:intro-radii` (`mat:T7`, `uct:admiss`, `mat:T3` proved); nothing else of C1 is needed. `ceo:O11ak` for general seeds is needed only for `thm:intro-gap` (iii), (iv) (M6, M8, `thm:ce-shifted-lift`); its one-level form, used by `uct:pos-floor` and `u1c:U3`, is done.
- **D1:** for `thm:intro-radii` the stop is `ceo:gauss.2`, `cel:L3a` (1)-(2) in the single-strip Dini form, the Mellin identity of `cepe:PE3` (all three done). The rest of D1 (post-edge, `ConvSource*` instance, `CeHankelPair`, packaging) is needed only for `thm:intro-gap` (iii) and the interim `thm_intro_radii`.
- **M6:** stop when `CeHankelPair` is proved (steps (b), (c)): it discharges `ce_hb_lift_m1` and gives the `m_0 = 1` case of `thm:ce-hb-lift` for `thm:intro-gap` (iii) and M8. It is not a stop for `thm:intro-radii`.
- **M10:** the interim deliverables are (a) `thm:ct-lower` (F1); (b) `fct:main-hankel` (F2a), which with F1 gives the five-term Hankel sign radii; (c) `fct:main-ce` (F2b), `gt:7.12a` (D2) and `thm:intro-radii`. M10 stops at (c).

Tier-2 items are not started while a tier-1 package is unstaffed.

### 2.5 Existing code to reuse (searched 2026-11-25; declarations read in the source)

- **F1, A3:** `ModularBootstrap/StripBand/StripPoissonRep.lean` (`stripPoisson_representation`), `Complex/StripPoisson.lean`, `Complex/HardyHalfPlane.lean`: the strip Poisson/Schwarz representation that `ct:outer` and `ct:dual-id` need. No Lean library has the strip outer function or the `ct:boas` identity; they are built here.
- **F2a, F2b, D1:** `Analysis/VanDerCorput.lean` (`van_der_corput_first`, `van_der_corput_second`; `fct:cusp-edge`), `Asymptotics/StirlingHalfInt.lean`; `CohnElkies/ConvSource*` and `CohnElkies/PreEdgeCriterion.lean` serve D1 only (no F2 result cites `ceo:conv` or `cepe:general`). Port selectively from `PrimeNumberTheoremAnd` (Apache-2.0, Lean v4.36.0): rectangle contour shifts (`ResidueCalcOnRectangles.lean`), `norm_fourier_le_integral_deriv_div`.
- **B1 (`gt:7.5` all levels), E1:** `Complex/Montel.lean` (`montel`) and `Analysis/Scheffe.lean` (`tendsto_integral_norm_sub_of_tendsto_ae`).
- **D2:** `Sphere-Packing-Lean` (Apache-2.0) `ForMathlib/RadialSchwartz/` (`RadialSchwartzMap`) is clean of proof placeholders and could serve `lem:ce-schwartz`; check against reasoner's `Euc d` and `FourierCompactSupport` first. Its `CohnElkies/LPBound.lean` rests on an unproved input and is not to be used.
- Newer Mathlib: reasoner is on v4.36.0 since 2026-11-25 (`fc4f59e`). Check whether the vertical Gamma bound (#45103) and `SchwartzMap.dense_hasCompactSupport` (#43046), which shorten C1 and D2, are in that tag; if not they wait for the next bump. `PrimeNumberTheoremAnd` (Lean v4.36.0) now matches the pin, so its rectangle contour shifts port without a version change.

## 3. Milestones

Names M0-M11 are kept. Size classes as in 6.1.

| milestone | content | packages | state | remaining |
|---|---|---|---|---|
| M0 skeleton | concrete definitions, headline statements, input structures (`RadiiInputs`, `ShellGapInputs`) | H | done | housekeeping (S): restate `thm_intro_gap_ii` without `ShellGapInputs`; decide the fate of the Route I leaves (section 1.3) |
| M1 classical leaves | real-order Bessel, Laguerre modes, radial Fourier transform on `Euc d` (even and odd `d`), Airy base | A1, A2, B2 | done | - |
| M2 Hankel layer | `hankelKernelData`, `gt:7.4`, `radial_compactness` | B1 | done | `gt:7.5` instance (S-M, with M8) |
| M3 strict gap, extraction half | `hankelShellGapLimit_proved`, one-profile problem, `even_m_laplace_sign` | E1 | done | origin-floor clause, endpoint case (S) |
| M4 upper O-chain at one level | `U.2`-`O.6`, `O.9'` at `m_0 = 1`; `o4QuotientBound` | C1, C2 | done | - |
| M5 Hankel lower half at one level | Langer chart, transport, band reduction, window, `hankelBootHB`; `hb_thresholds_lower` | B3, C3, A3 | done | `gt:7.7p` (d) clauses, weighted-Mellin clause of `u1cl:rep` (S-M, M8 prerequisite) |
| M6 CE upper, route II at `m_0 = 1` | `CeHankelPair`, hence `ce_hb_lift_m1` | D1 | in progress; `CeHankelPair` NOT proved | (a) done (`ceSourceFamily_convSource`, `ceLift_physical_unconditional`); remaining: (b) `thm:ce-post-edge` with `cepe:general` for `D_c`; (c) packaging, refactor `ceLift_physical` to expose both edge representations (L). Stop: `CeHankelPair` proved, which discharges `ce_hb_lift_m1` and gives the `m_0 = 1` case of `thm:ce-hb-lift` (`thm:intro-gap` (iii), M8); not a stop for `thm:intro-radii` (section 2.4) |
| M7 CE lower, shell reduction at one level | `shell_reduction_airy` | E1, D2 | done at `m = 1` | upper half is M6 |
| M8 all levels | `TE.0'` general, multilevel thresholds (`u1cl:multilevel`), `ShellReduction D`, `CeHbLift D` with weak positivity, positive odd families, `gt:7.5` general | A3, B1, B3, C2, C3, D1, E1 | not started | L; starts with a dependency list once M6 is merged |
| M9 Airy-LP core | `thm:airy-square-attained`, `thm:ce-airy-transfer`, `thm:ce-canonical-iff`, two-level Rayleigh, shifted lift, `cor:ce-schwartz-shells` | E2, D2 | planned, not started | L; needs only M3 |
| M10 constant terms | `thm:ct-lower`/`thm:ct-upper` five terms, density `eq:ce-density-exact`; carries the paper's `thm:intro-radii`. Interim deliverables, the stops: (a) `thm:ct-lower` (F1); (b) `fct:main-hankel` (F2a) with F1, the five-term Hankel sign radii; (c) `fct:main-ce` (F2b), `gt:7.12a` (D2), `thm:intro-radii` | F1, F2a, F2b, F3, D2, C1 | started: `ct:outer` complete, `ct:dual-id` (1) (`CtOuter*`, 45 files, about 10.7k lines; `CtDualIdBinet`, `Binet*`) | XL (F1, F2a, F2b; section 6.1), constants non-effective; the main lane: it carries the paper headline (owner rule, section 2) |
| M11 Hankel two-sided `O(1)` | `thm:hankel-one-two` from the two proved halves: `hankel_one_two` (`HankelOneTwo`) | C3 | done at one level | two-level (Clark) clause not formalised |
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

**Decided (owner, 2026-11-25): headline theorems first.** M10 is the main lane (it carries the paper's `thm:intro-radii`); M6 continues only as far as F2 (F2a, F2b) and `thm:intro-gap` (iii) need it; everything off a headline path is tier 2 (section 2).

**Agreements with the ModularBootstrap/FoldTip lane (Paper II plan, section 6).**
1. `HermiteBiehlerData` lives in the neutral module `SignUncertainty/HermiteBiehlerData.lean` (imports only `HermiteBiehlerUniq`); `RadialRigidity` re-exports it.
2. The base structure `ChartCompactness` (`compactness_subseq` plus site and tail positivity for an abstract setting) is owned by the fold-tip lane in a module importing nothing Hankel- or Virasoro-specific. It is **not on `master` yet**.
3. Paper I adds, without editing `RadialRigidity.lean`, a converter `RadialRigidityPackage -> ChartCompactness`, and plans M8's `TE.0'` (compactness for all `(P,Q)`) as a converter into `ChartCompactness` plus the shared rigidity theorem, not a second copy of the argument. Both start when `ChartCompactness` is on `master`.
4. The two rigidity proofs differ (profile compactness with Hermite-Biehler uniqueness here, vague limits of design measures there); only the interface is shared.
5. Langer charts and Mellin strips are separate objects in the two papers (Hankel/Bessel density `gt:7.7b/c/p` and `MellinStrip*` here; Virasoro comb density and `FixedWeightBand/Mellin*W` there). The Hankel `BootstrapHBInstance` follows the pattern of `FixedWeightBand/BootstrapW*`; Paper II does not refactor `ConcreteBootstrap/` or `TwoEdgeBootstrap/`, and Paper I does not edit `QuantC1Airy.lean`/`QuantC1Clark.lean` (Paper II's, imported here).
6. Fold-tip Theorem FT is part of Paper I (Section 4); its Lean code is `ModularBootstrap/FoldTip/`, and the Paper II plan has packages FT-0..FT-2 (done), FT-H4b and FT-CC (package G, section 6.1). It plans nothing beyond FT-CC for `FT-3..6` and has no `FT-7`: `ft:L1`, `ft:L2`, `ft:riesz`, `fto1:mellin` are planned here with M8 (section 1.3a). `lem:qual-compact` is not in Lean; it is the shared elementary step for `ft:L2` and the CE shell transfers (check `SignUncertainty/` before adding).

## 6. Coverage of the paper (reference)

Every stated result of Paper I is listed once: 165 rows = 162 `result` environments (132 in the 28 files of `CFT/sign_uncertainty/paper/` that contain one, 30 in the three `CFT/common/` files the paper `\input`s: `airy_poisson.tex` 16, `clark_airy.tex` 7, `two_edge_bootstrap.tex` 7; counted by script at QIprojects `2587d989b`, then adjusted for the paper cleanup of 2026-11-25: two results deleted, three added or promoted) plus the 3 introduction headline labels `thm:intro-radii`, `thm:intro-hb`, `thm:intro-gap`. These are aliases of results of other rows (`thm:ct-upper`, `u1cl:multilevel`, `thm:ce-canonical-iff`) and are kept as the rows of package H. Every other aliased label is one row, keyed by the first label. States are those of the rows of 6.2 on `master`, counted from those rows, and the counts of 6.1 are the same counts: **done** 48, **partial** 48, **planned** 68, **not planned** 1.

A row is **done** when the label is proved in Lean for the stated hypotheses (any difference in constants is noted), **partial** when some parts or instances are proved and the missing part is named, **planned** when a milestone owns it and nothing is stated (a result planned in this plan but staffed later is still planned), **not planned** with the reason. placeholders/`axiom`: none anywhere in `FormalResearch/` (grep on `master`), so no declaration cited here depends on a placeholder; "proved modulo fields" always means a named hypothesis structure.

### 6.1 Packages

| pkg | package | TeX | results | done / partial / planned / not planned | remaining size | inputs still taken as hypotheses | depends on | milestone |
|---|---|---|---|---|---|---|---|---|
| **A1** | Airy-Poisson defect formula, quadrature, sign uncertainty at the first node | `common/airy_poisson.tex` | 16 | 15 / 1 / 0 / 0 | - | none | - | M1 |
| **A2** | Clark-Airy and Hermite-Biehler quadrature, two-node theorem, Airy PWS | `common/clark_airy.tex` | 7 | 6 / 1 / 0 / 0 | - | none | A1 | M1 |
| **A3** | Two-edge bootstrap (strip Poisson, edge oscillation, Riesz-Airy-Poisson bootstrap, `C^1` stability) | `common/two_edge_bootstrap.tex` | 7 | 1 / 6 / 0 / 0 | L (all-`(P,Q)` `TE.0'` as a converter into the shared `ChartCompactness`; Hankel HB instance at every level) | Stage A is an instance obligation: `BootstrapInstance`, `BootstrapHBInstance`, `BootstrapCore` fields. Discharged for the Hankel one-level problem (`hankelBootHB`) and for Paper II problems; not for general `(P,Q)` Hankel | A1, A2, B3 | M8 |
| **B1** | Hankel layer: Mellin strip, radial compactness, rigidity | `fourier_mellin.tex`, `general_theorems.tex` | 3 | 2 / 1 / 0 / 0 | S-M (`gt:7.5` instance and `(P,Q)` form) | `gt:7.5`: `RadialRigidityPackage` fields | A2 | M2 |
| **B2** | Euclid-Hankel dictionary, Hardy-Mellin intertwiner, origin constraint | `general_theorems.tex` | 3 | 0 / 2 / 1 / 0 | S-M (every-`c` strengthenings; tier 2) | none | B1 | M1/M2 |
| **B3** | Langer chart, local density, transport, edge representation | `langer_transport.tex` | 5 | 3 / 2 / 0 / 0 | S-M (`gt:7.7p` (d), weighted-Mellin clause of `u1cl:rep`; `u1cl:langer` is done) | none (constants weaker than the TeX) | B1, C1 | M5, M8 |
| **C1** | Mellin-Airy toolkit and symbol transfer | `mellin_airy_toolkit.tex` | 11 | 5 / 6 / 0 / 0 | M-L, 1.5-2.5k (`uct:admiss`, general-seed `O.11ak`) | `ConvTailData` for general-seed `exists_hankelEigenfn_lift_general` | A1, A2 (`gt:3.1`), B1, C2, D1 | M4, M6, M10 |
| **C2** | Upper O-chain at one level (`U.*`, `O.*`, hb-seed-mass, `O.9'`) | `u1c_o1_upper.tex` | 13 | 5 / 8 / 0 / 0 | L (all-level `(P,Q)` seeds) | none for `hbThresholdsUpper`; `m_0 = 1` only | A1, A2, B1, C1 | M4, M8 |
| **C3** | Hankel thresholds: one-level halves, multilevel theorem, two-sided `O(1)` | `u1c_o1_lower.tex` | 2 | 1 / 1 / 0 / 0 | L (all levels); S (`u1cl:main`) | none at one level | A3, B3, C2 | M5, M8, M11 |
| **D1** | Cohn-Elkies upper half, route II: convolution source, transfer, pre-edge, post-edge, lift | `ce_hb_lift.tex`, `ce_o1_route.tex`, `ce_o1_global_transfer.tex`, `ce_o1_pre_edge.tex`, `ce_physical_log_far.tex`, `ce_rate.tex` | 16 | 6 / 7 / 3 / 0 | L (post-edge sign L; packaging S-M; the `CeSourceFamily` instance is done) | `PreEdgeGeneralData`, open `CeHankelPair` (`CeSourceFamily` is proved) | by the TeX citations: A1 (`ap:E3`), A2 (`gt:3.1`, `gt:1.0pp`), C1 (`mat:T1`, `T3`-`T5`, `cegt:GT1`, `GT2a`, `ceo:O11ak`), C2 (`u1c:U1`-`U3`, `u1co:O2`, `O3`, `O5`, `O6`, `lem:hb-seed-mass`), E1 (`thm:ce-laplace-zeros`, `lem:airy-laplace-general`), `gt:7.10` (the admissible class with logarithmic decay; not planned); by the Lean: B2 (`EuclidHankelDictionary`), E1 (`ShellHBData`); E2 (`lem:ce-terminal-deflation`) for the tangency lifts of M8 | M6, M8 |
| **D2** | Cohn-Elkies radius layer: finite dimensions, Schwartz vs `L^1` infimum, density | `ce_finite_bounds.tex`, `ce_radius.tex` | 6 | 1 / 2 / 2 / 1 | S-M | `ce_radius_airy_order_of_bounds` takes both halves as hypotheses (`hlo`, `hhi`) | B2 | M7, M9, M10 |
| **E1** | Cohn-Elkies shells: reduction, extraction, one-profile, odd families, Laplace zeros | `ce_shells.tex`, `ce_projection_mass.tex`, `ce_radius.tex` (2 results) | 8 | 2 / 5 / 1 / 0 | M (`ShellReduction D`); M-L (positive odd families) | `ShellReduction D` for `m >= 2`; none for the extraction and one-profile parts | B1, B2, C3 | M3, M7, M8 |
| **E2** | Limiting Airy program at prescribed shells (Airy-LP) | `ce_airy_lp.tex`, `ce_airy_lp_proofs.tex`, `ce_canonical_iff.tex`, `ce_two_level.tex`, `ce_shifted_witnesses.tex`, `airy_extremal.tex`, `ce_radius.tex` (2 results: `lem:deflation-identity`, `lem:ce-terminal-deflation`) | 24 | 0 / 0 / 24 / 0 | L-XL (about 24 results, 1,106 TeX lines; calibration: `ShellLaplaceBase` 1.9k + `OddShellFamily` 1.4k lines) | - | A1, A2, E1 (M3) for the Airy-LP core; D1, C1, C2 for `thm:ce-shifted-lift` | M9 |
| **F1** | Five-term lower bound for the Hankel thresholds | `constant_terms_lower.tex` | 7 | 0 / 1 / 6 / 0 | XL (805 TeX lines, section 6.1 note; calibration: the Virasoro lower half took about 29k lines) | - | A2 (`gt:1.0p`), B1, B3 (incl. `u1cl:langer`), C1, A3, M11 | M10 |
| **F2a** | Five-term upper bound for the Hankel thresholds, with the lemma chain that F2b reuses | `constant_terms_upper.tex` (6 results), `constant_terms_five.tex` (14) | 20 | 0 / 0 / 20 / 0 | XL (1,648 TeX lines; no Hankel-only part apart from `fct:main-hankel`, so there is no shared package F2s: section 2.1) | - | F1 (`ct:outer`, `ct:cfu`, `ct:dual-id` (1), `ct:morse-expansion`, the equation `ct:langer-inv`), A2 (`gt:3.1`), C1 (`mat:T1`, `T3`, `T4`, `uct:admiss`), C2 (`u1c:U2`, `U4a`, `u1co:O3`-`O5`), D1 (`ceo:gauss.2`) | M10 |
| **F2b** | Five-term upper bound for the Cohn-Elkies radius | `constant_terms_upper.tex` (3: `uct:outer-growth`, `uct:gen-preedge`, `uct:ce-band`), `constant_terms_five.tex` (3: `fct:main-ce`, `fct:ce-band`, `fct:ce-preedge`) | 6 | 0 / 0 / 6 / 0 | XL (477 TeX lines, the lower edge of XL) | - | F2a, F1 (`ct:outer`, `ct:dual-id` (1)), C1 (`mat:T3` (5), `T4`, `uct:admiss`), D1 (`ceo:O11n.7`, `cel:L3a`, `cel:total-saddle`, `cepe:PE3`), D2 (`lem:ce-schwartz`, empty strict set: in Lean) | M10 |
| **F3** | Five-term theorem `thm:ct-upper` (assembly and reductions; since PR 295 the proof also gives `T_c^- <= T_c^CE` for real `c` from the negative eigenprojection, the only new step being that the Hankel transform of a compactly supported `h` is entire, and `T_c^CE = r_CE(d)^2/2` for integer `d` by `gt:7.9b`, radial averaging and `lem:ce-schwartz`) | `general_theorems.tex` | 1 | 0 / 1 / 0 / 0 | S | F1, F2a (part (i), the sign radii of (ii)), F2b (the CE radius of (ii)); `RadiiInputs` for (iii) | B2, D2, F1, F2a, F2b | M10 |
| **G** | Fold-tip universality (Theorem FT and the two-edge versions) | `fold_tip_universality.tex`, `fold_tip_two_edge.tex`, `fold_tip_two_edge_hb.tex` | 9 | 0 / 3 / 6 / 0 | `ft:FT`, `ft:WP`, `ft:WR`, `fto1:sub`, `fto1:thm`: the ModularBootstrap/FoldTip lane (`ModularBootstrap/PLAN.md`: FT-0..FT-2 done, FT-H4b, FT-CC); `ft:L1`, `ft:L2`, `ft:riesz`, `fto1:mellin`: this plan, with M8 (section 1.3a) | violator family and chart coverage as hypotheses; `FTH4b` mismatch | A3, Paper II instances | FT lane |
| **H** | Introduction headlines (aliases since PR 287, see 1.1; the introduction `sign_uncertainty_core.tex` has no result environment) | aliases in `general_theorems.tex` (`thm:ct-upper`), `u1c_o1_lower.tex` (`u1cl:multilevel`), `ce_canonical_iff.tex` (`thm:ce-canonical-iff`) | 3 | 0 / 2 / 1 / 0 | S per theorem after its inputs | `RadiiInputs` (open: `ce_hb_lift_m1`), `ShellGapInputs` (open: `shell_reduction`, `ce_hb_lift`) | see section 2 | all |

The "Lean today" column of each package (declaration families and size) is in 6.2 below, one table per package. Size classes, in Lean lines for the remaining work: S < 500, M 500-2000, L 2000-10000, XL > 10000, calibrated on existing files: `CEShellReduction` 227, `HankelThresholds` 147, `ShellLaplaceBase` 1,939, `OddShellFamily` 1,375, the whole one-level Hankel lower half (`Hankel*`) about 17.6k, `O4*` 2.7k, `ConvSource*` 3.2k, `ShellGap*` 2.7k.

**TeX-line basis of XL.** For each `\begin{result}`, the lines up to the next result, remark or section command (statement, proof and the text between them; counted by script on QIprojects `2587d989b`), plus, for the two main theorems of F2, their assembly passages (`constant_terms_five.tex` lines 1221-1384, 1385-1456 and 1722-1724); 1,987 of the 2,125 lines of F2a and F2b are neither blank nor comment. Finished packages give about 27-80 Lean lines per such TeX line (`B3` 187 TeX lines, about 6k Lean; `D1` 745, about 20k; `C1` 357 and `C2` 311, about 25k each), so F1 (805 TeX lines) is at least 20k, F2a (1,648) at least 40k and F2b (477) at least 12k. The same count gives E2 1,106 TeX lines, so its class below is L to XL; it is not revised here.

### 6.2 Results by package

**A1. Airy-Poisson defect formula, quadrature, sign uncertainty at the first node** (`common/airy_poisson.tex`). Lean: `Special/AiryCft*` (about 8k lines), `AiryKernel*`, `AiryTransform*`, `AiryEnvelope*`, `Complex/Hardy*`.

| label | state | Lean today / note |
|---|---|---|
| `ap:E1` | done | `airyAiC_envelope` |
| `ap:E2` | done | `good_circle_exists`, `good_circle_airyAiC_ne_zero` |
| `ap:E3` | done | `airyEnv_add_real_le` |
| `ap:E4` | done (dead in the paper: cited only in prose and by a dead remark) | `airyPhi_norm_le` |
| `ap:thmD` | done | `airy_defect_bound`, `airy_defect_ball` |
| `ap:corD1` | done | `airy_quadrature` |
| `ap:lemU` | done | `airyQG` (unfolding `u = -z^2`) |
| `ap:lemH` | done | `hardy_integral_zero`, `hardy_value_le` (the inequalities used; Hardy spaces are not defined) |
| `ap:lemHp` | partial | `airyQ_mem_half`, `airyQ_pointwise_uniform` give the `f in L^1`, `s = 0` form; the shifted form `s > 0` is not stated |
| `ap:lemFR` | done | `hardy_arc_le` |
| `ap:thmQ` | done | `airyQ_defect_bound_int`, `airyQ_pointwise_sharp`, `airyQ_sampling`, `airyQ_hasSum_unc` |
| `ap:corQp` | done (dead in the paper: cited only in prose and by a dead remark) | `airyQ_vanishing_moment`, `airyQ_vanishing_moment_decay` |
| `lam:Q1` | done | `airyQ_hasSum_unc` |
| `lam:Q2a` | done | `airyKer`, `airyKer_eq_integral`, `airyKer_diag_le` |
| `lam:Q2` | done | `airyPW_reproducing`, `airyPW_parseval`, `airyClassG_PW_mul` |
| `lam:thmB` | done | `airy_sign_uncertainty`, `airy_sign_equality_iff`, `airyExtremal_attains` |

**A2. Clark-Airy and Hermite-Biehler quadrature, two-node theorem, Airy PWS** (`common/clark_airy.tex`). Lean: `Special/AiryPoly*`, `AiryThm47*`, `AiryClark*`, `AiryPws*`; `SignUncertainty/ClarkTwoNode`, `HermiteBiehlerUniq`, `HermiteBiehlerData`.

| label | state | Lean today / note |
|---|---|---|
| `gt:1.0` | done | `airyNC_good_circle` (since PR 295 the paper derives it as the uniform constant case of `gt:1.0p`; nothing to change in Lean) |
| `gt:1.0p` | done | `airyPQ_good_circle`, `airyPQ_good_circle_SE5` |
| `gt:1.0pp` | done | `airyPQ_hasSum_unc`, `airyPQ_tendsto_of_simple` |
| `lem:hb-uniqueness` | partial | `hb_uniqueness`, `hb_two_node_l1_norm`, `airy_m1_uniqueness`: the terminal case `J = {1..m}` (now the paper's "in particular" clause). Since PR 295 the lemma classifies `H in G` with `int H >= 0`, `H(t_n) <= 0` and `H'(t_n) = 0` off any finite `J` as `N^2 R / prod_J (t_j - u)`, `deg R <= |J| - m` (same Cauchy estimate, exponent `|J| - m + 1/2 - l`, plus a converse); the general form is M9 (it feeds `lem:airy-even-node-obstruction`), S |
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
| `lem:finite-hankel-compactness` | planned | tier 2 (PR 293: stated for every real `c > 1/2`, using only `|K^{(c)}| <= 1` and the Bessel decay `O((Delta s)^{1/4-c/2})`; the Mellin estimates stay at `c >= 1`): fixed-`c` compactness of normalized pairs (Bessel decay, equicontinuity, Scheffé); reuse `Analysis/Scheffe`, `radial_compactness` |
| `gt:7.9a` | partial | (PR 293: now for every real `c > 1/2`; the vanishing midpoint moment `int f s^{c/2-1} = 0` is the Gaussian identity `g^_b = b^{-c} g_{1/b}` integrated against `b^{c/2-1} db` with `b -> 1/b`, no Mellin strip; the finiteness competitor is `u_{b_2}/(1-b_2^{-c}) - u_{b_1}/(1-b_1^{-c})`, not a Laguerre combination) `intertwiner_feasible`, `threshold_pos_le_neg`, `fourier_radii_pos_le_neg`: non-strict `T_c^{+1} <= T_c^{-1}`; the strict inequality with attainment (3) is tier 2 |
| `gt:7.9b` | partial | `hankelT0_eq_hankelT`, `laguerre_odd_mode`, `isRadialEigenfn_oddLaguerreMode_bessel`, under `T_c^{-1} > c/(4 pi)` (enough for `thm:ct-upper`); every real `c > 1/2` (reciprocal-scale Gaussian `b^{-c}e^{-2 pi Delta/b} - e^{-2 pi b Delta}`), attainment, zero origin of every minimizer and precompactness are tier 2 |

**B3. Langer chart, local density, transport, edge representation** (`langer_transport.tex`). Lean: `HankelLanger*`, `HankelStrip*`, `HankelLocal*`, `HankelTail`, `HankelTransport*`, `HankelEdge*` (about 6k lines).

| label | state | Lean today / note |
|---|---|---|
| `gt:7.7b` | done | `HankelLangerU/Y/Real/ChartMain` (`u = zeta^2` form), `HankelLangerIdentity` |
| `gt:7.7c` | done | `HankelLocalDensity`, `HankelLocalEnvelope` (envelope `(e71)`), `HankelLocalHolo` |
| `gt:7.7p` | partial | `hankelPsi_cut_bound`, `hankelPsi_deriv_bound` (`HankelPsiCutBound`, explicit non-TeX constants), `hankel_tail_le`, `hankel_psi_neg_mass`, `HankelTransport*` for `c >= 3e6` with weaker constants (tail `c/40000`); the explicit cut-crossing constant and the two-level `C^1` stability (`alpha != 0`) of part (d) are not stated |
| `u1cl:langer` | done | `u1cl_langer` (`HankelLangerComparability`); band clause at `zeta = i tau_0`, not as a limit |
| `u1cl:rep` | partial | `HankelEdgeRep`, `HankelStripInversion`, `HankelBandInstance` for the one-level Hankel problem; the weighted-Mellin clause (`u1cl:weighted-mellin`) is not stated |

**C1. Mellin-Airy toolkit and symbol transfer** (`mellin_airy_toolkit.tex`). Lean: `CohnElkies/Mellin*`, `AirySymbolTransfer`, `SeedSymbolDerivs`, `Gt1*`, `MiddleBand*`, `MellinLift*`, `Asymptotics/BinetRemainder` (about 25k lines).

| label | state | Lean today / note |
|---|---|---|
| `mat:T1` | done | `muBin_pos`, `binetDiff_norm_le`, `binetRem_iteratedDeriv_norm_le` (`Asymptotics/BinetRemainder`) |
| `mat:T2` | done | `mellin_strip_kernel_eq`, `norm_mellinK0_imag_le` |
| `mat:T3` | done | (1): `stripG_hasSum`, `stripGCoeff_pos`, `stripGReal_bijOn`, `stripGReal_deriv_bounds` (`MellinT3Taylor`); (2) `(e35)`: `norm_c_mul_stripS0Tilde_le`, `two_mul_stripS0Tilde_e35Radius_lt`; (3): `mellinPhi_re_vertical` (all real `τ`), `im_stripG_eq`, `im_stripG_ge`; (4): `im_stripG_ge_gaussian`, `mellinUpsilon_hasDerivAt`, `mellinUpsilon_gaussian_bound`; (5): `integral_im_stripG_ge`, `mellinUpsilon_integrated_bound`, `mellinUpsilon_zero_eq` |
| `mat:T4` | done | `edgePhiDeriv_ge`, `edgePhiDeriv2_abs_le`, `edgePhiDeriv3_abs_le`, `m1_bound`, `m2_bounds`, `ceGamma_strictMonoOn` |
| `mat:T5` | done | `fourier_L1_le_sqrt_mul`, `fourier_L1_le_sqrt_mul_H1` |
| `cegt:GT1` | partial | `gt1BasisInput` (basis seeds `f_1, g_1, g_1'` times the spline multiplier, `m >= 3`); other seed families not stated |
| `cegt:GT1s` | done | `gt1s_scalar_airy_symbol_transfer` |
| `cegt:GT2a` | partial | `middle_transfer_gt1` for `HasU2` seeds (cut in `tau`, not in `theta` as in the TeX); the hypothesis `Gt1Bounds` is supplied by `gt1BasisInput` |
| `mat:T7` | done | `mat_T7_a`, `mat_T7_b`, `mat_T7_c`, `mat_T7` (`MellinStripLift`; `StripW1`, `StripW2` = (W1), (W2)) |
| `ceo:O11ak` | partial | `exists_hankelEigenfn_lift` (one-level seeds, `m >= 3`); `exists_hankelEigenfn_lift_general` (general seeds) takes `ConvTailData`, now proved for the convolution source (`convTailData_convSource`, `ceLift_pair_convSource`, `ConvSourceEdge*`) and for one-level seeds (`convTailData_airySeedU2`); the fixed-`c` `L^1`-kernel form is not stated |
| `uct:admiss` | done | (1), (2): `uct_admiss` (under the weaker `StripAdmissData`); (3) and the whole lemma: `uct_admiss_part3`, `uct_admiss_full` (`StripAdmissFullData` = (M1)-(M3) at both edges) |

**C2. Upper O-chain at one level (`U.*`, `O.*`, hb-seed-mass, `O.9'`)** (`u1c_o1_upper.tex`). Lean: `CohnElkies/AirySeedFloors`, `AirySeedSymbols`, `PieceC*`, `HighBand*`, `DualBoundE3`, `CubicNormalForm*`, `O4*`, `MiddleBand*`, `WindowTranslation`, `HbUpperM1` (about 25k lines).

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
| `u1co:O4` | done | `o4QuotientBound` (analytic estimate on `|θ| = 1/4`), `o4_normal_form`, `CubicNormalFormH` |
| `u1co:O5` | partial | (e5) `window_translation_airySeed` for `c >= 32768` (TeX: `c >= 200`); (e6) `o5_e6`, `o5_e6_airySeed` |
| `u1co:O6` | partial | `o6_positivity` with `O6Est`; bricks discharged for the one-level seed by `o6Bricks_holds` (`m >= 3`) |
| `lem:hb-seed-mass` | partial | `hb_seed_mass_exists` for any `HBSeedSpec`; only the `m_0 = 1` witness `hbSeedSpec_airy_witness` exists |
| `u1co:O9p` | partial | `hbThresholdsUpper` (`m_0 = 1`, `N = Ai`); all-level `(P,Q)`: planned M8 |

**C3. Hankel thresholds: one-level halves, multilevel theorem, two-sided `O(1)`** (`u1c_o1_lower.tex`). Lean: `HankelThresholds` (`hb_thresholds_lower`), `HbUpperM1` (`hbThresholdsUpper`), `HankelBoot*`, `HankelWindow*`, `HankelQuantC1*`, `HankelBand*`.

| label | state | Lean today / note |
|---|---|---|
| `u1cl:multilevel` | partial | one level: lower half `hb_thresholds_lower`, upper half `hbThresholdsUpper`; all `(P,Q)` and the `f(0) = 0` clause: planned M8 (no `HbThresholds` declaration exists) |
| `u1cl:main` | done (one level) | `hankel_one_two` (`HankelOneTwo`); the two-level Clark clause is not formalised |

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
| `ceo:gauss` | done | `airySquare_gaussian_transform` (`ceo:O11n.7`), `airyTwistedLaplaceC_ceG1_eq` (`ceo:gauss.1`), `ceG1_twisted_bounds` (`ceo:gauss.2`: `b(1+x)^{-9/2} <= g1~ <= C(1+Re z)^{-9/2}`, `CeGauss2`) |
| `ceo:conv` | partial | `ConvSource*`: `convS_bounds`, `HasU2`, `gt1Bounds_convSource` (O.12(1)-(4)), `ConvTailData` for `S_c` (`ConvSourceEdge*`), and all five `CeSourceFamily` fields (`ceSourceFamily_convSource`, `ConvSourceFamily`, weak forms of `edge`, `dual`); open: the sharp O.12(5), O.12(6) (needed by `PreEdgeGeneralData`), the uniform far transfer O.12(7), GT.2b and `ceo:gauss.2` (no Lean statement) |
| `ceo:O11ae` | done | `MellinMainKernel` (`bsplineMult`, `mainEdgeAmp`, `norm_mainEdgeAmp_le`) |
| `cepf:FG3` | done | `Tc_sup_bound`, `fourier_L1_le_sqrt_mul_H1`, `mainTransferOp_sup_norm_le` |
| `cepf:PF3` | done | `pf3_kernel_bound`, `pf3_kernel_bound_uniform` |
| `cel:L3a` | partial | (1) all kernel bounds (`OriginMellinAndS0`, `CeGenOrigin`: `norm_gamma_mul_ceOriginE_le`, `ceOrigin_phase_quad_bound`, `hInt_sub_linear_bound`); (2) for a single-strip multiplier with a Dini modulus: `IsDiniModulus`, `ceOrigin_shift_dini`, `ceOrigin_shift_dini_of_W1`, `ceOriginG_conj` (`G_c(-iy) = conj G_c(iy)`); Hölder versions re-derived in place (`ceOrigin_shift`). Open: the two-edge multiplier `W_S + W_D` (only M6 / `thm:intro-gap` (iii) needs it) |
| `cel:L4` | done | `SaddleGeometry` (items (2), (3) as in the TeX) |
| `cel:L5` | partial | `lobe_saddle_asymptotic` (two-edge, stated with `C_* = 150`), first-order total form `cel:total-saddle`: `lobe_total_saddle` (`C_* = 150`). Missing: second-order `cel:total-saddle-2` (input of `cepe:abs-saddle`) |
| `cel:L7` | done | `integral_cos_sq_ge` (`SaddleGeometry`) |

**D2. Cohn-Elkies radius layer: finite dimensions, Schwartz vs `L^1` infimum, density** (`ce_finite_bounds.tex`, `ce_radius.tex`). Lean: `CohnElkies/{FiniteDimensionCrossings,FiniteGaussianBase,CohnElkiesRadius}`.

| label | state | Lean today / note |
|---|---|---|
| `thm:ce-gaussian` | done | `ce_quadratic_dimensions` (`FiniteDimensionCrossings`, `FiniteGaussianBase`) |
| `lem:ce-schwartz` | partial | the `X = empty` case: `ce_schwartz_radius_eq_L1_radius`, `ce_schwartz_bound_eq_optimalCohnElkiesBound`; strict signs at a finite shell set `X` are not stated |
| `gt:7.10` | not planned | owner-deferred; not on any headline path (the packing bound for integrable CE pairs) |
| `cor:ce-schwartz-shells` | planned (tier 2: cited only by the remark `rem:ce-compact-shells`; not an input of `thm:ce-canonical-iff`) | M9 (needs the sequence proofs of `thm:ce-airy-transfer`; a compact-set statement since PR 291) |
| `prop:ce-finite-attainment` | planned | tier 2 (PR 291, 293: stated for Hankel pairs at real `c > 1/2`, shell sets `S` bounded away from zero, terminal radius `sqrt(2T)` in integer dimensions; since PR 295 it also records that `T_c^CE` is finite, positive and attained for every real `c > 1/2` (Gaussian pair); `thm:ce-gaussian` is now `h_c(Delta) = (1 - 2 a_d Delta) e^{-2 pi t_d Delta}` with `w(Delta) = h_c(b^2 Delta)`): weak continuous-integrable CE attainment at fixed `d` with compact positive shells (dilated Gaussian `H_d(bx)` restores origin equality); needs `lem:finite-hankel-compactness`, `ce_quadratic_dimensions` |
| `gt:7.12a` | partial (a separate D2 leaf: the abstract states the density formula under `thm:intro-radii`, but `thm:ct-upper` and its proof never cite `gt:7.12a`) | `thm_intro_radii_ce`: `c_1 <= vol <= c_2` and the log law up to `O(1)`; the exact five-term density `eq:ce-density-exact` needs M10 |

**E1. Cohn-Elkies shells: reduction, extraction, one-profile, odd families, Laplace zeros** (`ce_shells.tex`, `ce_projection_mass.tex`, and from `ce_radius.tex` `thm:ce-laplace-zeros`, `lem:airy-laplace-general`). Lean: `ShellGap*` (about 2.7k lines), `ShellLaplaceBase`, `ShellLaplaceZeros`, `OddShellFamily`, `CEShellReduction`, `OneProfileEnvelope`, `HeadlineDefs`.

| label | state | Lean today / note |
|---|---|---|
| `thm:ce-shell-reduction` | partial | `shell_reduction_airy`, `shell_reduction_m1_proved` (`m = 1`); the general `ShellReduction D` is the open field of `ShellGapInputs`: M8 |
| `thm:ce-physical-profile` | partial | extraction form `hankelShellGapLimit_proved` (mass ratio, tails, Laplace limit, transport, Mellin reflection); the origin-floor clause and the endpoint case `u_* = t_m` are not stated |
| `par:ce-one-profile` | done | `one_profile_feasible_iff`, `one_profile_threshold_le_and_endpoint_iff`, `one_profile_maximizer_exists` (with `AiryCompactnessModel`, built from `one_profile_envelope`) |
| `thm:ce-shell-gap` | partial (the `u_* = t_m` endpoint clause and the origin floor are not formalised) | `hankelShellGapLimit_proved`, `shellGapLimit_of_hankel`; `thm_intro_gap_ii`, `thm_intro_gap_ii_even` (the statement carries an unused `ShellGapInputs` argument) |
| `cor:ce-projection-mass` | done | inside `hankelShellGapLimit_proved` (the constraint system `eq:ce-laplace-constraint`); no separate statement |
| `thm:ce-odd-family` | partial (advertised in the abstract: strict gap at every odd number of levels > 1; cited by no theorem proof, so a leaf of `thm:intro-gap` rather than an input) | `ce_odd_family_laplace_gap`, `odd_shell_family_laplace_gap` (Laplace-negative odd families); the Laplace-positive odd families (attainment at every odd `m`) are not stated: M8 |
| `thm:ce-laplace-zeros` | partial | `laplace_zero_multiplicity_le`, `laplace_zero_analyticOrder_le`, `laplace_pos_near_zero`, `laplace_pos_large_of_odd`, `laplace_m3_classification`; endpoint clause not audited |
| `lem:airy-laplace-general` | planned | M9 (`ce_radius.tex`; filed under E1 beside `thm:ce-laplace-zeros`, which cites it; also cited by `ce_hb_lift.tex` (D1) and `ce_airy_lp_proofs.tex` (E2)): Laplace sign-change count (Rolle; since PR 295 also improved to `n - M - 1` when `M + 1` moments vanish, used by `lem:airy-even-node-obstruction`) and large-height asymptotic `L_y(H) ~ C 2^{2p} sqrt(pi) y^{1/2-2p}`; check `ShellLaplaceBase`, `ShellLaplaceZeros` (`laplace_pos_large_of_odd`) for parts before adding |

**E2. Limiting Airy program at prescribed shells (Airy-LP)** (`ce_airy_lp.tex`, `ce_airy_lp_proofs.tex`, `ce_canonical_iff.tex`, `ce_two_level.tex`, `ce_shifted_witnesses.tex`, `airy_extremal.tex`, and `lem:deflation-identity`, `lem:ce-terminal-deflation` from `ce_radius.tex`). Lean: none (inputs in Lean: `airyNC_quadrature`, `hb_uniqueness`, `one_profile_*`, `hankelShellGapLimit_proved`, `airyAiC_logDeriv_mittagLeffler`, Clark two-node `AiryCft2Clark`).

| label | state | Lean today / note |
|---|---|---|
| `lem:qual-compact` | planned | M9/M8 (S lemma shared with the fold-tip blow-up `ft:L2`); not in Lean; check `SignUncertainty/` before adding |
| `thm:airy-square-attained` | planned | M9: statement in `ce_airy_lp.tex`; proof in `ce_airy_lp_proofs.tex` |
| `thm:ce-airy-transfer` | planned | M9: parts (1) two-sided bound, (2) exact coefficient, (3) stability, (4) uniformity on compacts (PR 291, 293: (4) is for shell families `S_{c,S}` with `d_H(S_{c,S}, S) -> 0` uniformly on a compact family of compact sets, a compact-set statement; `rem:ce-compact-shells` gives the robust coefficient `lim_{delta -> 0} liminf/limsup_d rho_d(S_delta) = -u_sh(S)/beta_1` and a diagonal choice `delta_d` along continuity points of `F(delta) = u_LP(S_delta)`, common to the four infima; repeated sites are covered by Newton divided differences) |
| `lem:al-seeds` | planned | M9 |
| `lem:al-smooth` | planned | M9 |
| `lem:al-reference-positive` | planned | M9 |
| `lem:airy-shell-buffer` | planned | M9 |
| `lem:airy-active-height` | planned | M9 ((1) since PR 295: a buffer with `L_B > 0` at the finitely many positive zeros of `L_H` suffices) |
| `lem:airy-square-bound` | planned | M9: uses `airyNC_quadrature` and Mittag-Leffler `airyAiC_logDeriv_mittagLeffler` (both in Lean); since PR 295 stated per trial cutoff `v`, with square constraints only at the sites above `v` |
| `lem:al-kernel` | planned | M9: Christoffel-Darboux (`lam:Q2a`) plus Parseval in `PW`; since PR 295 the proof no longer cites `lem:ce-rayleigh-two-level` (a citation cycle removed); `Special/AiryTransform*` has the orthonormal basis at the Airy zeros and Parseval |
| `prop:airy-secular` | demoted | cited only in prose and as a parallel of `lem:ce-rayleigh-two-level`; not used by `thm:airy-square-attained` (usage audit); keep only as a remark |
| `lem:airy-node-square` | planned | M9 (fixed square since PR 291; the Dirichlet gap of `rem:ce-nonhb-gap` is now derived from `thm:airy-square-attained` instead of repeating the strictification) |
| `lem:airy-even-node-obstruction` | planned | M9 (new in PR 295, `ce_airy_lp_proofs.tex`): a nonzero `H in G` nonpositive on a left ray and at every node of `N` with `L_H >= 0` forces odd level `m`; so a shell set containing the first `p - 1` nodes of an even-level rule has `u_LP < t_p`. Inputs: general `lem:hb-uniqueness`, `lem:airy-laplace-general` (1) with moments, Airy asymptotics on the negative axis. Replaces the ad hoc proof in `rem:airy-even-deep-gap`, M |
| `thm:airy-node-sign` | planned | M9 |
| `lem:al-hermite-approx` | planned | M9 |
| `lem:al-far-cardinal-laplace` | planned | M9 |
| `thm:al-rational-density` | planned | M9 |
| `lem:deflation-identity` | planned | M9 |
| `lem:ce-terminal-deflation` | planned | M9 |
| `thm:ce-canonical-iff` | planned | M9: (1)-(2), aliases `prop:airy-strictification`, `lem:airy-last-gap` |
| `thm:ce-shifted-lift` | planned | M9: the CE lift of strict shifted rational-Airy witnesses (route-II machinery at shifted nodes) |
| `lem:ce-rayleigh-two-level` | tier 2 | used only by `cor:ce-rayleigh-bound` (usage audit); not needed by `thm:ce-airy-transfer` or `thm:ce-canonical-iff` |
| `cor:ce-rayleigh-bound` | tier 2 | advertised in the abstract (Neumann bracket) but cited by no theorem or proof; item (3) rests on a 300-bit ball enclosure (`verify_ce_rayleigh_two_level.py`); not a leaf of `thm:intro-gap` |

**F1. Five-term lower bound for the Hankel thresholds** (`constant_terms_lower.tex`). Lean: `CtOuter*` (45 files, about 10.7k lines; `ct:outer`, complete), `CtDualIdBinet`, `Binet*` (`ct:dual-id` (1)); other inputs in Lean: `HankelLanger*`, `gt:7.4`, `radial_compactness`, `hankel_quantC1_of_feasible`, `hankelBootHB`).

| label | state | Lean today / note |
|---|---|---|
| `ct:outer` | done | `ct_outer_part1`, `ct_outer_part2_structure`, `ct_outer_part2_taylor` ((1), and the structure of (2): `theta_eps` odd, smooth, holomorphic on `|tau| < 1/2`, Taylor to order 5), `theta_one_minus`, `theta_one_plus`, `theta_three_eq`, `ct_outer_part2_taylor_values` ((2) with the paper's constants, `CtOuterTheta1`, `CtOuterTheta3`), `ct_outer_part3` ((3): asymptotics and both derivative bounds, `CtOuterPart3Plus`; through the boundary functional of `Im h~`, a smooth cutoff and Cauchy estimates, without a complex local-continuation lemma). All unconditional |
| `ct:dual-id` | partial | (1) proved: `ct_dual_id_part1` (`CtDualIdBinet`, `Binet*`: vertical-line decay `|d^r B_c(i tau)| <= C_r/(c(1+|tau|)^{r+1})`, holomorphic extension to `Im tau > -1`, `ct:binet-small`); (2), the exact Cauchy duality identity, open: needs the Mellin-Whittaker representation `ct:Wc-rep`, the class `A_c^eps` with `dm(xi)` and `Phi_Ph` with the (M1)/(M2) bounds, and a van der Corput lemma (`Analysis/VanDerCorput.lean` has the first and second derivative tests) |
| `ct:cfu` | partial | Step 2 data done: `cfu_psi_langer`, `langer_inv` (`CtCfu*`; `ψ_ε` `C^∞`, not analytic, at `a = 0`). Step 4 (outer band) done for `μ₀ ≥ M`: `ct_cfu_outer`, `outer_band`, `stat_phase`, `outerAmp_ampBd` (`CtOsc*`, `CtOuterBand*`, about 4,400 lines). Step 1 (Airy identities `ct:airy-id1`, `ct:airy-id2`) done: `G_eq_HH`, `airy_id1`, `airy_id2` (`CtAiry*`). Step 3 chart done: the chart `T(s;β)`, `M`/`Q_geo`, the `θ∘T` decomposition, `Q_0` and the `Q_ε` expansion (`CtChart*`, `β = b²` parametrisation, germs at `(0,0)`), and its link to the real Step 2 data (`psiHat_link`: `ψ̂(z_A a) = ψ(a)`, `a_C = a`, `exp(L_C)/π² = Ξ`). Step 3 steepest descent in the `w`-plane done in abstract form (`CtSd*`: complex Binet bound, `sqrt_primitive` path independence, the moment bounds `ct:sd-moments` for both contours, integration by parts, `sd_eval`). Remaining: deformation of the real-axis integral to `Γ_SD ∪ Γ_arc` with the arc/tail double integration by parts, the tail beyond `R` and the match of the chain integrals with `airy_id1`/`airy_id2`, assembly of `ct:K-airy` and `ct:theta-cfu-match`; then the bounded-`μ₀` range via `ct:dual-id` (2) |
| `ct:dyadic` | planned | M10 (lower bound) |
| `ct:boas` | planned | M10 (lower bound); via the finite Fejér inequality `ct:fejer`; Step 1 is the analytic continuation of the Gaussian identity of `gt:7.9a` |
| `ct:phase-far-lem` | planned | M10 (F1): new lemma (2026-11-25), the outer-band phase `c Phi(tau_0) = 2 pi Delta - pi c/4 + O(Delta e^{-2 pi^2 Delta/c})` for `Delta >= c >= 1`; used by `ct:boas` |
| `ct:morse-expansion` | done | `morse_expansion` (`CtMorse*`, unconditional; by induction on `r` with a Hadamard quotient, not the paper's Taylor/Abel sketch); input of `ct:cfu` Step 4 and of F2a `fct:warp-asymp` |

**F2a. Five-term upper bound for the Hankel thresholds, with the lemma chain that F2b reuses** (`constant_terms_upper.tex`: 7 results; `constant_terms_five.tex`: 12). Lean: none (inputs in Lean: `U.2`-`O.5` at one level, `airySquare_gaussian_transform`, `exists_hankelEigenfn_lift`).

| label | state | Lean today / note |
|---|---|---|
| `fct:main-hankel` | planned | M10 (upper bound): the Hankel assembly; its construction passage (`fct:s4-proof`, `fct:tab-regimes`, `fct:hg1-win`, `fct:hg1-mac`) is reused by F2b. Step 1 (admissibility) checks `uct:admiss` for the floor multiplier `W_pos` by integration by parts, `(g_1')~(i w) = -w g_1~(i w)`, then `uct:g1-int`, `uct:Fstar-int` near the edges and `u1c:U2` (1) at large height (PR 295 review; `uct:pos-floor` (2) alone does not give (M3)); dependency closure in the paragraph below the F2a tables |
| `fct:moment-solver` | planned | M10 (upper bound): finite moment correction, any fixed number of moments (polynomial zero counting) |
| `fct:comp-D` | planned | M10 (upper bound) |
| `fct:phikill` | planned | M10 (upper bound) |
| `fct:comp-cfu` | planned | M10 (upper bound): compensated cubic chart via a scalar cubic and implicit differentiation; main (2026-11-26) adds explicit `C^k` chart estimates and a rigorous zero solve in Prop. `FCT.5`(1) |
| `fct:inner-symbols` | planned | M10 (F2a): new Lemma FCT.5b (main, 2026-11-26): Airy-type oscillatory integrals and the inner amplitude on the zero-solve box (`fct:RI-bounds`, `fct:chain`); `fct:psi-real` (FCT.9 Step 1(b), real-axis equivalence) is now proved uniformly |
| `fct:warp-asymp` | planned | M10 (upper bound); 5, 21, 7 integrations by parts through `fct:edge-ibp` |
| `fct:edge-ibp` | planned | M10 (F2a): new Lemma FCT.5a (2026-11-25), Abel-sense edge-cutoff removal and shoulder IBP uniform in the regulator `lambda in {0, 1/c}`; shared by `fct:warp-asymp` and `fct:ce-band` |
| `fct:splitting` | planned | M10 (upper bound) |
| `fct:bump-5` | planned | M10 (upper bound) |
| `fct:bump-sym-check` | planned | M10 (F2a): Lemma FCT.7b (a remark until 2026-11-25); symbol-class bounds of the three bumps, cited by `fct:physical-positive`, `fct:main-hankel`, `fct:ce-band` |
| `fct:cusp-edge` | planned | M10 (upper bound): absolute edge estimate for a cusp profile (three integrations by parts, van der Corput; reuse `Analysis/VanDerCorput`) |
| `fct:unscaled-cusp` | planned | M10 (upper bound) |
| `fct:physical-budget` | planned | M10 (upper bound): common physical bump budget for Hankel and CE |
| `fct:physical-positive` | planned | M10 (upper bound): four-band physical-edge positivity criterion |
| `uct:airy-trans` | done (except two unused ray identities) | `UctAiryTrans*`: representations, asymptotics with all derivatives, origin expansion, real/local/vertical bounds; the ray identities `int_{S+-} s^{-1/2} e^psi = 0`, `(2 sqrt pi)^{-1} int s^{1/2} e^psi = 1` are not formalised (used only to rotate a contour, replaced by an ODE/barrier argument) |
| `uct:pos-floor` | done | `UctPosFloorSeed/UctPosFloor/UctPosFloorTail/UctPosFloorWpos`: (1) `uct_pos_floor_one`; (2) `uct_pos_floor_main`, `uct_pos_floor_lift`; (3) `airyTwistedLaplace_uctSpos_floor`, `uct_pos_floor_pre_edge` (uniform in `delta_0 > 0`, `m = 4`; `m >= 1` in `uct_pos_pre_edge_gen`) |
| `uct:strip-split` | done modulo small-`L` expansions | `UctStripSplit`, `UctStripIntegrals`: (1) `uct_H_split`, `uct_HCE_signs`; (2) `uct_strip_split_integrals`; (3) `uct_strip_split_ratios` (`r_CE, r_h < 1`, `1 - r_CE >= min(L,1)/6`). Not formalised (used by nothing): the expansions `47/20`, `13/20`, `13 pi^2/240`, `19 pi^2/240` |
| `uct:bump-symbol` | partial (densities done) | `UctBumpSymbol`: `bump_laplace_decay` (the first display, `BumpProfile` = the TeX hypotheses). `UctBumpSymbolAdmiss`: `bump_stripM1` (M1), `bump_holder_one` (M2). `UctBumpEdge`: (M3) at both edges, `bump_stripAdmissFull = StripAdmissFullData (1/2)`. `UctBumpMain`: `bump_main_density` (main density, `L <= b delta/2`, `sigma = k sqrt(delta)`). `UctFourierTwice`, `UctBumpReflEll/Amp/B`, `UctBumpRefl`: `bump_refl_density` (reflected density, `L^-2` for `L >= 1`, via `ct:binet-decay`). Open: the Fourier identity `(uct:E0-def)` |
| `uct:bump-weighted` | planned | M10 (upper bound): weighted Taylor inversion (`uct:weighted-taylor`) and uniform far-band bound `O(M(1+c^{-2} delta^{3-alpha}) c^{-2} L^{-2})` |
| `uct:bump-est` | removed | deleted from the paper 2026-11-25 (no proof cited it; superseded by `fct:bump-5` at the scale `delta_L ~ c^{-1/2}`) |
| `uct:seed-asymp` | done (item (1)) | `UctSeedAdmiss`: `seedW_stripAdmissFull` (the (M1)-(M3) verification of `W^seed`, `StripAdmissFullData (1/2)`), with `UctSeedZ`, `UctSeedW`, `UctSeedWHolder`, `UctSeedEdge*`. `UctSeedEdgeKW`: `kw_seed_edge_all` (`(uct:KW-seed-edge)`), `uctAstar`, `uctMc`; `UctMcSmall`: `mc_small` (`(uct:Mc-small)`). `UctSeedWindow`: `seed_window` (item (1), the fixed Airy window: `|h_norm^seed - (k/c_s)F_{*,δ}(-β₁S_eff+β₁κ_εc^{-1/3})| ≤ C_{S_w}c^{-2/3}`, via `UctSeedWindowDiff/Sym/Y/Q/Ref`; done). Item (2) (middle band) is not formalised (see M10 below); items (3)-(4) are not used. M10 (F2a): only items (1)-(2) are used, by proof reuse for `g~_1` (`fct:main-hankel`, `fct:main-ce` repeat its proof of (2)); items (3)-(4) are demoted (cited only as a foil and a convention in `fct:warp-asymp`; paper cleanup: demote to a remark) |

**Dependency closure of `fct:main-hankel` (F2a, 2026-11-26; script over the merged text at qi-f2a `50ecf0f86`: the statement and the proof of Theorem FCT.1 (`fct:s4-proof`, l.1363-1526), then each cited result's own statement and proof; "used by", "vs." and table mentions are not dependencies).** Bottom-up, with the cited parts:
- *Inputs outside F2a (done or other lanes):* `ct:outer`, `ct:dual-id`, `ct:cfu`, `ct:morse-expansion`, `ct:theta-form`, `ct:five-term-node`, `ct:langer-inv` (F1); `mat:T1`-`T5`, `T7`, `uct:admiss` (1)(2), `u1c:U2`, `U4a`, `u1co:O3`-`O5`, `ceo:O11ak`, `ceo:gauss.2`, `ceo:O11n.7`, `gt:3.1`, `cel:5.5`.
- *Level 1, `uct:*` already done:* `uct:outer-growth`; `uct:airy-trans` (1)-(3); `uct:pos-floor` (1)-(3); `uct:strip-split` (2)(3); `uct:seed-asymp` (1) done, (2) middle band open (cited via `fct:hg1-mid`, and by proof reuse for `g~_1`).
- *Level 2, `uct:*` open:* `uct:bump-symbol` (main density and reflected density done; `(uct:E0-def)` Fourier identity open) and `uct:bump-weighted` (weighted Taylor inversion, far band). Both are reached only through `fct:bump-5` (items (1), (2), (3) = `bump-symbol`, `bump-weighted`, `bump-weighted`).
- *Level 3, `fct:*` without `fct:*` inputs or with only these:* `fct:moment-solver`; `fct:phikill` (1)(3); `fct:edge-ibp` (1)(2); `fct:cusp-edge`; `fct:comp-D` (`moment-solver`, `uct:strip-split` (2)(3); cited parts (1)(2), `p=1,2`, the alpha-component); `fct:comp-cfu` (`comp-D`, `moment-solver`, `ct:cfu`; cited at lambda = 1, L = L_1).
- *Level 4:* `fct:inner-symbols` (a), (b1)-(b4) (`comp-D`, `comp-cfu`, `phikill`, and the box data of `warp-asymp` (1)); `fct:warp-asymp` (1)(2)(3) (`comp-D`, `comp-cfu`, `edge-ibp`, `inner-symbols`, `phikill`; `ct:outer`, `ct:morse-expansion`, `ct:theta-form`; mentions `physical-positive` (iii) and `ce-band` only in a regime remark, l.853).
- *Level 5:* `fct:splitting` (1)(2) (`comp-D`, `phikill`, `warp-asymp`); `fct:bump-5` (1)-(3) (`uct:bump-symbol`, `uct:bump-weighted`, `uct:admiss`); `fct:unscaled-cusp` (`comp-D`, `warp-asymp`); `fct:physical-budget` (`comp-D`, `phikill`); `fct:bump-sym-check` (c) (`bump-5`, `comp-D`, `phikill`); `fct:physical-positive` (iii) (`bump-5`, `bump-sym-check`, `physical-budget`, `warp-asymp`).
- *Level 6, the Theorem FCT.1 proof itself:* `fct:bump-5`, `bump-sym-check` (c), `cusp-edge`, `physical-budget`, `physical-positive` (iii), `splitting` (1)(2), `unscaled-cusp`, `warp-asymp`; `uct:admiss`, `airy-trans`, `pos-floor` (2), `seed-asymp` (1)(2); `u1c:U2` (1).
- *Not dependencies of `fct:main-hankel`* (F2b only): `fct:main-ce`, `fct:ce-band`, `fct:ce-preedge`, `uct:ce-band`, `uct:gen-preedge`. `fct:main-ce` adds exactly these to the closure above (plus `uct:strip-split` (2)(3), `uct:outer-growth`, `ct:outer`, `cel:L3a`, `lem:ce-schwartz`, `mat:T4`).
- *`fct:comp-cfu` versus F1's `CtChart*`:* different construction. `CtChart*` is the analytic complex germ of `ct:cfu` at `(0,0)` (qualitative `C^infty`, `scalar_ift`). `fct:comp-cfu` is a real chart on the fixed scaled box `(Y, l, lambda, alpha)`, with `C^14` bounds `O(c^{-1/2})`, the lambda-homotopy ODE and perturbation jets, resting on a quantitative `C^k` implicit-function Claim G; only the algebraic identities (divided-difference equation, `key_identity`, saddle normalisation) transfer.

**F2b. Five-term upper bound for the Cohn-Elkies radius** (`constant_terms_five.tex`: `fct:main-ce`, `fct:ce-band`, `fct:ce-preedge`; `constant_terms_upper.tex`: `uct:outer-growth`, `uct:gen-preedge`, `uct:ce-band`). Lean: none (inputs in Lean: `lobe_saddle_asymptotic`, `cel:L3a`/`L4`/`L7` in the two-edge form).

| label | state | Lean today / note |
|---|---|---|
| `fct:main-ce` | planned | M10 (upper bound): the CE assembly, built on F2a. Since PR 295 it is stated for real `c` (`T_c^CE <= Delta_5^-(c) + C c^{-3/4}`) and no longer cites `gt:7.12`; the integer-`d` radius uses only `lem:ce-schwartz` with empty strict set (in Lean: `ce_schwartz_radius_eq_L1_radius`). Its proof now has an explicit admissibility step (`uct:admiss` for every summand of `fct:Wce-negh`, citing `ct:outer` (3), `fct:phikill` (1), `fct:comp-D` (1), `fct:F-38-bnd`), so `ct:outer` (3) is an F2b input |
| `fct:ce-band` | planned | M10 (upper bound): the same two-regime argument as `fct:warp-asymp` (3) (one lemma in Lean); applies the maximum principle to `g_D''` citing `fct:comp-D` (1), stated for `g_D`, `g_D'` only (section 1.3a) |
| `fct:ce-preedge` | planned | M10 (upper bound); uses `uct:gen-preedge`, `uct:ce-band`, `ct:dual-id`, `cel:L3a` |
| `uct:outer-growth` | done | `UctOuterGrowth`: `norm_exp_neg_outerHbar_le`, `outerGbar_inv_le`, `outerHbar_zero/one`, `exists_holo_H1` (disc bounds off the closed strip not stated separately). Also needed by `uct:seed-asymp` (the `W^seed` admissibility) |
| `uct:gen-preedge` | done | `uct_gen_preedge` (paper form, `c ≥ 60`, `StripAdmissFullData (1/2) W`) and the sharp forms `existsUnique_saddlePoint`, `uct_gen_preedge_saddle_of_M1`, `uct_gen_preedge_pos_of_M1` (part (1) needs only (M1)), `uct_gen_preedge_origin_of_holder` (part (2) needs only `c ≥ 2`, (M1), (M2) at `ζ=1` for any `α > 0`) (`UctGenPreedge`); cited only by `fct:ce-preedge` |
| `uct:ce-band` | planned | M10 (upper bound); combined holomorphic amplitude `A = e^{i theta} M` on a lower half-disc, `A(0) = 1` |

**F3. Five-term theorem `thm:ct-upper` (assembly and reductions)** (`general_theorems.tex`). Lean: reductions in Lean: `hankel_euclid_dictionary`, `intertwiner_feasible`, `ce_schwartz_radius_eq_L1_radius`, `ce_quadratic_dimensions`, `hankelT0_eq_hankelT`.

| label | state | Lean today / note |
|---|---|---|
| `thm:ct-upper` | partial | (iii) (all `d >= 2`, Airy order, `O(1)`) is the Lean `thm_intro_radii` shape, conditional on `RadiiInputs` (open `ce_hb_lift_m1`); (i) (now including `T_c^CE`), (ii) five-term bounds: M10. The proof of the lower bounds for the integer radii moved here from `constant_terms_lower.tex` (PR 295) |

**G. Fold-tip universality (Theorem FT and the two-edge versions)** (`fold_tip_universality.tex`, `fold_tip_two_edge.tex`, `fold_tip_two_edge_hb.tex`). Lean: `ModularBootstrap/FoldTip/*` (about 2.3k lines); `TwoEdgeBootstrap/FoldTipSeed`.

| label | state | Lean today / note |
|---|---|---|
| `fto1:sub` | partial (cited by no headline: only its own sub-equation; Paper II notes mention it) | `ft_sub`, `ft_sub_displacement`, `ft_sub_feedback` (same hypothesis) |
| `fto1:thm` | partial | `ft_twoEdge_lower`, `ft_twoEdge_expansion`, `ft_twoEdge_lower_hb`: over the abstract two-edge bootstrap, the violator family as a hypothesis |
| `fto1:mellin` | planned | M8, this plan (with `TL6`); needed by the lower half of `u1cl:multilevel` (section 1.3a) |
| `ft:FT` | partial | FoldTip lane: hypotheses H1-H4b as structures; conclusions for Paper II instances `ft_fixedWeight_general`, `ft_fixedWeight`, `ft_virasoro`, `ft_n1`; the Lean `FTH4b` does not match the paper (FT-H4b first FT target) |
| `ft:L1` | planned | M8, this plan (the Paper II plan does not plan `FT-3..6` beyond `FT-CC`, section 1.3a) |
| `ft:L2` | planned | as `ft:L1` (uses `lem:qual-compact`) |
| `ft:riesz` | planned | as `ft:L1` |
| `ft:WP` | planned | FoldTip lane, FT-H4b |
| `ft:WR` | planned | FoldTip lane, FT-H4b |

**H. Introduction theorems** (aliases of `thm:ct-upper` in `general_theorems.tex`, `u1cl:multilevel` in `u1c_o1_lower.tex`, `thm:ce-canonical-iff` in `ce_canonical_iff.tex`; the introduction `sign_uncertainty_core.tex` states them in prose). Lean: `SignUncertainty/Headlines.lean` (`thm_intro_radii`, `thm_intro_gap_i`-`_iii`); the retired separation bound is in `SignSeparationLimsup.lean`.

| label | state | Lean today / note |
|---|---|---|
| `thm:intro-radii` | partial | Lean `thm_intro_radii`/`_sign`/`_ce`: the `O(1)` Airy-order radii and the density up to constants (shape of `thm:ct-upper` (iii) and `gt:7.12a`), conditional on `RadiiInputs`; the five-term statement is not stated |
| `thm:intro-hb` | planned | M8; no Lean statement (`HbThresholdsLower`, `HbThresholdsUpper` are the one-level halves) |
| `thm:intro-gap` | partial | `thm_intro_gap_i`, `_ii`, `_ii_even`, `_iii` (conditional on `ShellGapInputs`; (ii) does not use it); (iii) only for strict Laplace positivity; (iv) not stated: M9 |

### 6.3 Remarks that state something

Remarks are not counted above. The ones that carry content: `thm:ce-neumann` (Remark H.14c, the Neumann shell: recorded without proof in the paper, nothing depends on it; **not planned**); `rem:airy-even-deep-gap` (explicit data with `t_{m+k} < u_sh <= u_LP < t_{m+k-1}`, a remark with proof, small; planned with M9); `prop:odd-shell-certificate` (Remark: explicit odd-level instance by an exact-ball certificate; **not planned**: `ce_odd_family_laplace_gap` covers existence); `mat:T6` (symbol bounds for rational Airy functions: used through `Gt1NegTailAmp`, in Lean in the form `gt1BasisInput` needs); `uct:quintic-barrier`, `uct:rem-var`, `fct:rem-mech`, `fct:rem-num`, `ct:rem-split`, `ct:rem-lattices` (explanatory or numerical cross-checks: **not planned**; a finite-`c` numerical check is numerical evidence, never a Lean statement).

Further remarks with content (checked in the TeX at `2587d989b`):
- `fct:bump-sym-check` (Lemma FCT.7b (a remark until 2026-11-25), `constant_terms_five.tex`): proves the symbol-class bounds `fct:B-sym` for the three constructed bumps `B_c^eps`, `B_{-h}`, `B_{hhat}` (common factors, compensator and curvature factors, decomposed pieces). It is cited four times (`fct:physical-positive`, the proof of `fct:main-hankel`, `fct:ce-band` twice), so it is a step of the F2 proofs: **planned** with F2a (M10).
- `rem:ce-dirichlet-gap` (`ce_airy_lp.tex`): for finite Dirichlet nodes `D_0`, `p = min{n : a_n not in D_0}` and `S = D_0 u C` with `C` compact in `(-inf, a_p)`, `u_LP(S) = a_1` and `u_sh(S) = a_p`, so the gap is arbitrarily large; a short proof from `thm:airy-square-attained`, `rem:ce-compact-shells` and the strictification of `lem:airy-square-bound`: **planned** with M9.
- `rem:ce-nonhb-gap` (`ce_airy_lp.tex`): a non-Hermite-Biehler example (three sites, weight `1 + 10 e^{5u/2}`) with `u_LP - u_sh >= 0.36513` by an outward-rounded ball-arithmetic certificate; the paper says the analysis is not used or proved there: **not planned** (computer-assisted, outside the article).
- `ceo:O11ak.rem` (Remark O.11ak.a, `mellin_airy_toolkit.tex`): the explicit form of `ceo:O11ak.4`, `|xi (L rho_0)(c xi)| <= c^{-1/3}(M_1 l^{-3/2} + M_2 l^{-2})` for `l = log(pi^2 xi) >= 2` with `M_1`, `M_2` named from the proof, and the resulting `Delta^{-c} (log Delta)^{-3/2}` bound for `L_c^sigma[X]` and `h` on `R^d`: it follows from the proof of `ceo:O11ak` (C1); **not planned** separately, since Lean's constants are existential.
- `teb:quant_c1_near` (Remark TE.0 flat, `common/two_edge_bootstrap.tex`): the near-threshold form of `teb:quant_c1` at `alpha = 0` (the threshold may lie within `K_1 c^{-1/3}` below `a_1`), which the TeX states is `teb:quant_c1_hb` (1), (3) for `(P,Q) = (1,0)`, `m_0 = 1`, `d_c = K_1 c^{-1/3}`. No Paper I result cites it; Paper II's FIVE-L needs it (`ModularBootstrap/PLAN.md`, section 6): **not planned** here.

Not result labels: `ceo:O11n.7` is a displayed equation inside `ceo:gauss` (there is no label `ceo:O11n`); `ct:langer-inv` is a displayed equation of the CFU discussion in `constant_terms_lower.tex` (between `ct:dual-id` and `ct:morse-expansion`), not inside a result environment; `cepe:PE3` is an item inside the proof of `cepe:general`. A plan row for any of them would be keyed by the enclosing result.

