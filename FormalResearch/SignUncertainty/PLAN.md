# Paper I (Fourier sign uncertainty, Cohn–Elkies) — Lean plan

Source: QIprojects `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex` (+ supplement, `CFT/common/`).
Supersedes the "Wave 10–12" plan left after Wave 9 (`7ae7af6`). Audit date 2026-11-23, reasoner `778feac`.

## 1. Where we are

- 64 files, about 64k lines (CohnElkies about 40k, SignUncertainty 14k, TwoEdgeBootstrap 4k, Asymptotics 3k).
  `lake build FormalResearch.SignUncertainty FormalResearch.TwoEdgeBootstrap` passes (9269 jobs, about 9 min). There are no
  placeholder proofs or custom axioms, and the headline theorems use only the standard three axioms.
- **No headline result of Paper I is Lean-checked, not even conditionally on a TeX theorem.** The four introduction
  theorems are `thm:intro-radii` (sign-uncertainty radii plus `gt:7.12` CE radius), `thm:intro-separation` (`gt:7.9c`),
  `thm:intro-hb` (`thm:hb-thresholds`) and `thm:intro-gap` (`thm:ce-shell-gap`).
  - The Hankel problem now has its concrete kernel: `hankelKernelData (hc : 1/2 < c)` is unconditional (`HankelBessel*`,
    real-order Bessel in `Special/Bessel*`), and the `±1` Laguerre modes of `gt:7.9b` are proved eigenfunctions
    (`HankelBesselLaguerre`).
  - `CohnElkiesRadius.ce_radius_airy_order_of_bounds` is only the gluing step. Its hypotheses `hlo` and `hhi` *are* the
    two halves of the theorem, and the module imports none of the Airy or Mellin machinery.
- **Waves 4–9 (about 25k lines) feed only leaves.** About 30 hypothesis packages (`MacroscopicTransferPackage`,
  `GT4CoverageBands`, `PE3OriginData`, `PreEdgeGeneralData`, `AiryTailSymbolSeed`, `MovingDiagFarTail`, `ShellGapPackage`,
  …) have only toy non-vacuity witnesses (all functions 0, constants 1, or degenerate parameters), and none has a real
  instance. `MovingDiagFarTail` has no instance at all. Theorems such as GT.2b, GT.3b, GT.4, PE.3 and `cepe:general` are
  stated for an abstract `fhat` that carries the paper's estimates as hypotheses. Nothing builds `W_S`, `W_D` from `Ai`,
  or `h_mellin` from a CE pair.
- Open skeleton fields in `Headlines.lean` (9): `hankel_euclid_dictionary`, `hb_thresholds_lower`,
  `hb_thresholds_upper`, `shell_reduction_m1`, `ce_hb_lift_m1`, `shell_reduction`, `shell_gap_limit`,
  `one_profile_envelope`, `ce_hb_lift`. `radial_compactness` is a theorem and no longer an input.
- What is genuinely closed and reusable:
  - the Airy base: Theorems D, Q and B with its equality case, Clark two-node, Hermite–Biehler quadrature and
    `at47_*`, and Airy PWS (a)⇔(b);
  - E.1–E.3a (finite dimensions);
  - H.14a and H.14b;
  - `lem:radial-compactness` (`radial_compactness`: Mellin inversion, deep lobe, Montel, Airy-class limit, Fatou) and
    the radial rigidity proof `gt:7.5` from it;
  - the strip Poisson kernel TE.1/TE.1a, the algebra of Bootstrap Stage B, Binet and T.1–T.4;
  - GT.1/GT.1s, O.0–O.2, O.3(1), U.4a, O.11h/j/p/x/n and the pieces of CR.1–CR.4.

## 2. What was wrong with Waves 10–12

1. **Bottom-up with no consumer.** Each wave proves a lemma family under packaged hypotheses, and nothing checks
   that the package is the one a headline needs. The result is many conditional statements and zero headlines.
2. **The plan targets both CE upper routes.** `ce_radius.tex` proves the upper half of `gt:7.12` by
   `thm:ce-hb-lift` with `m₀ = 1` (Route II). Wave 10 also targeted the coherent-square lift `thm:ce-lift` (Route I):
   the GT.4 coverage bands, PF.2, PF.5 and `prop:ce-pre-edge`. Route II needs none of these (checked in the TeX:
   `ce_hb_lift.tex` cites O.11w, CR.4, `lem:hb-seed-mass`, U.2, GT.2b, O.11ak, O.6, `thm:ce-post-edge`, `cepe:general`,
   O.11x, O.11n and `cel:L2a`; post-edge uses GT.2a and GT.3a/b, and GT.3b uses PF.T, PF2L.2, PF.4 and FG.3a).
3. **The base shared by every headline is missing from the plan.** The plan never mentions:
   - the concrete Hankel/Bessel kernel of real order;
   - `gt:7.4` (Mellin strip and majorant);
   - `lem:radial-compactness`;
   - the Langer chart `gt:7.7b/c/p`;
   - the Euclidean ↔ Hankel dictionary (radial Fourier on `Euc d`, including odd `d`; `O(d)` averaging;
     Bourgain–Clozel–Kahane / Cohn–Gonçalves reduction).
4. Wave 12 puts general de Branges (SE.1–SE.5) and `PW·PW` on the path. No headline needs them.

## 3. Strategy

- **Skeleton first (M0).** State each headline in Lean with the paper's constants, on concrete objects:
  - `optimalL1CERadius` (exists);
  - Euclidean `A_sign^±(d)`;
  - Hankel thresholds `T^±_{m,c}` with the real Bessel kernel.

  Prove each headline from one input structure whose fields are, one-to-one, the TeX theorems it cites (for
  example `hb_thresholds_lower`, `ce_hb_lift_m1`, `shell_reduction_m1`, `hankel_euclid_dictionary`). Progress is the
  number of skeleton fields still open. A field is closed only when it is discharged by a theorem about the concrete
  objects.
- **Every new module must close or shrink a skeleton field.** Existing packages are either wired into a field's
  proof (instantiated with the real Airy cardinal kernel and real CE data) or deleted (git keeps them). Toy
  witnesses do not count as progress.
- **Cheapest unconditional headlines first, then by sharing.** The strict gap and the separation need only the Hankel
  layer and the one-level upper bound, so they come before the Langer/bootstrap lower half. `thm:intro-radii` at one
  level (`gt:7.9` + `gt:7.12`) is the main target and reuses all of it.

## 4. TeX changes made first (QIprojects branch `papers/p1-route-cleanup`)

- **T1 done (owner decision).** The coherent-square lift (`thm:ce-lift`, GT.0, GT.2, GT.4 + tip profile, `prop:ce-pre-edge`,
  O.11y, PF.2, PF.5, O.11aw, coherent amplitudes) is now the supplement part `ce_coherent_square_lift.tex`, outside Lean scope.
  The paper's transfer appendix keeps what the hb-lift uses, stated for a general seed: the fixed-window formula, absolute
  reflected integration, GT.2b, GT.3a/b and post-edge. Its source is the new Lemma O.11s (`ce_o1_route.tex`: `S_c = θ S_h + γ ε S_0`,
  mass and local/far asymptotics, from O.11w). In Lean, `MacroscopicTransferPackage` needs only the fields GT.3b uses;
  `GT4CoverageBands` and the PF.2/PF.5 consumers are out of scope.
- **T2 verified.** At `m₀ = 1`, `H_N = g₁` and the seed is `F_δ = −f₁ − γ₁δ g₁ + γ₂δ(g₁ + g₁' − f₁) + r_δ g₁`, a combination of three
  Airy squares (now stated in `ce_radius.tex`). U.2, GT.1 and T.6 are needed only for `f₁`, `g₁`, `g₁'` and the source.
- **T3: no change needed.** The internal proof header of `gt:7.9c` lists only what the proof uses.
- **T4 done.** Lemma 7.7c cites `gt:7.4(2)`, which holds for either sign; the circular-looking citation of `thm:hb-thresholds`
  is gone.
- **T5 is Lean-only.** The TeX treats odd `d` as half-integer `c` in the Hankel problem. Lean still needs radial Fourier in odd `d`.
- **Also changed:**
  - The intro now states the prescribed-shell results as a dichotomy (`thm:intro-gap` (i)–(iii)): the O(1) lower bound,
    the strict gap if `L_y(−G_N) < 0` for some `y`, and O(1) attainment for odd `m` with strict Laplace positivity. This is
    the natural M0 skeleton statement for Headline D, with `m = 1` being the CE radius.
  - App F (general de Branges) and E.2–E.3a moved to the supplement. They are not in Lean scope.

- **T6: shorter routes after an external review (agy, checked by independent referees).**
  - `gt:7.9c` no longer uses Langer transport or `thm:hb-thresholds`: `lem:radial-compactness` now converges with first
    derivatives, and the upper half is the one-level O.9′.
  - The hb-lift source is a left-shifted convolution of `g₁` (merged, QIprojects `4d1eeda37`); the Dirichlet diagonal,
    CR.1–4, PF.2L, PF.T and W.0–W.6 move to the supplement with Route I.
  - U.3(3)/O.3(2) by real-line integration by parts and Fresnel; O.4(2) by a Banach contraction with a certified bound
    (merged).
  - H.14a now also gives Laplace-positive odd families, so `thm:intro-gap` (iii) occurs at every odd `m`; intro (ii)
    states the bound `−u_LP/β₁`.

## 5. Milestones (S < 500 lines, M 500–2000, L > 2000; calibration: the Virasoro lower half took about 29k lines)

The order puts the cheapest unconditional headlines first. The strict gap (M3 below) and the separation (Headline S) need only
the Hankel layer, the one-level upper bound and pieces that already exist; the heavy analysis (O-chain, Langer,
bootstrap) comes after them.

**M0 Skeleton (S–M).**
- Concrete definitions and the four headline statements, each proved from its input structure.
- Fix two semantic gaps in existing packages: `SignSeparation.lean` defines `A_sign(d)` as `√(2 T_{d/2})` (the Hankel
  threshold), not the Euclidean infimum; `ShellGapPackage` enforces exact zero-offset shells and quantifies over one
  package, not the infimal `R_d^{CE}` with `o(c^{1/3})` offsets.
- `LangerSignSeparationPackage.langer_approx` is no longer needed (TeX `gt:7.9c` no longer uses Langer); replace it by
  the `C¹` compactness field.
- Delete or archive the dead packages: `GT4CoverageBands`, the PF.2/PF.5 consumers, `MovingDiagFarTail`, the CR.4 and
  PF.2L packages once the convolution source lands.
- Rename overclaiming names (`theorem_H14_strict_gap` → `…_core`; `teb_mellin_o1_lower` docstring).

**M1 Classical leaves (parallel; independent of everything else).**
- Bessel `J_ν` for real `ν`: bounds and Weber integral DLMF 10.22.43; Laguerre modes `(4πΔ/c−1)e^{−2πΔ}` (eigenvalue
  −1) and `e^{−2πΔ}` (+1) (M–L).
- Radial Fourier transform on `Euc d`: even `d` exists (`ModularBootstrap/.../HankelFormula.lean`,
  `fourier_radialLift_apply_eq`); close even-`d` headlines first and do odd `d` in parallel (M). `O(d)` averaging.
- `hNicholson` and `hBesselRatio` are dropped: they served only the Dirichlet-diagonal source (CR.4, W.0–W.6), which
  the convolution source replaces.

**M2 Hankel layer (used by every headline; L).**
- Concrete `HankelKernelData` from M1; `gt:7.4` (strip reflection, majorant, three lines).
- `lem:radial-compactness` with the `C¹` clause (the kernel's `s`-derivative is the same integrand times `(w−ε²)/ξ_c`).
- `gt:7.5` (blow-up limit via `hb_uniqueness`, which exists).

**M3 Headline C′: strict gap `thm:intro-gap` (ii) (M–L).**
- Laplace limit L.6 (Stirling and majorants); compactness for `p_c`, `q_c`; `o(c^{1/3})` offsets and the infimal
  radius; the one-profile bound `−u_LP/β₁` (`prop:ce-one-profile`). Downstream (`ShellHBData`, `even_m_laplace_sign`,
  `OddShellFamily`) exists. Needs only M2.

**M4 Upper O-chain at one level (shared by everything below; L, technical core).**
- U.2 for `{f₁, g₁, g₁'}`, U.3, GT.2a (on its Fourier-side hypotheses), O.5, O.6, O.11ak (Mellin-lift hub), O.9′ at `m = 1`.
- O.3(2)/U.3(3): real-line subtraction of the `x^{−3/2}` tail, two integrations by parts and the Fresnel integral (no
  Puiseux, no V-ray). U.1 only in its closed-half-plane form.
- O.4(2): Banach contraction for the cubic normal form (`ContractingWith.fixedPoint`), with the certified bound on the
  circle as an interval-arithmetic input; no branched cover or monodromy.

**Headline S: separation `gt:7.9c` (S–M after M2, M4).** `gt:7.5` + `C¹` compactness + one-level O.9′ give the slope
window; the intertwiner and its tail positivity exist (`HardyMellinIntertwiner`, `sign_separation_*`). No Langer chart,
no bootstrap.

**M5 Hankel lower half at one level (L).**
- Langer chart `gt:7.7b/c/p` (Rouché exists). The Type (I) cut bound follows by subharmonic averaging as in Step 0 of
  TE.0, so the separate `Re ζ = c^{−1/3}` contour shift can be skipped in Lean.
- TE.0 at one level: adapt `teb_quant_c1_typeII` (already a compactness argument) to Type (I). This is non-effective,
  which is fine for Lean; the TeX keeps the effective version (Paper II needs it).
- TE.3 Hankel window and `BandReductionInstance`; discharge the `BootstrapCore/Instance` fields starting from the
  general-weight bootstrap of Paper II (`ModularBootstrap/FixedWeightBand/BootstrapW*`, `BandBoundW*`), which already
  generalises the Virasoro `ArcBounds`/`QuadratureBounds` instance; do not refactor the Virasoro files. L.2/L.6 at one
  level. (Paper II's Langer chart and Mellin strip are different objects from the Hankel ones here; no overlap.)

**Headline A, `gt:7.9`:** M2 + M4 + M5 + the Euclidean reduction (BCK/CG, averaging, finite `d` via E.1; M).

**M6 CE upper, `thm:ce-hb-lift` at `m₀ = 1` with the convolution source (M).**
- Source `S_c = ∫₀^∞ w_c(y) g₁(u+y) dy`: product formula for its twisted transform, symbol bounds of the weight, far
  transfer GT.3b by Fourier–Sobolev, pre-edge bounds from the single-term Gaussian identity (exists:
  `airySquare_gaussian_transform`).
- `thm:ce-post-edge` and `cepe:general` stated for a general source; hb-lift assembly (seed mass `m₀ = 1` exists); lift
  to `Euc d`. This gives `hhi`.

**M7 CE lower (M).** Shell reduction `m = 1`, `O(d)` averaging, and the Hankel lower half from M5 give `hlo`.

**Headline B, `gt:7.12` + `gt:7.12a`, unconditional.** This completes `thm:intro-radii`.

**M8 All levels (L).**
- TE.0′ by the same compactness argument for all `(P, Q)` (`hb_uniqueness` exists); TE.2(4) instance; general
  `HBSeedSpec` (`gt:1.0pp`); multilevel L.2.
- This gives `thm:intro-hb`, general `thm:ce-hb-lift`, and `thm:intro-gap` (iii) with its odd-level examples (H.14a).

**Deferred (not on any headline path):**
- Route I (`thm:ce-lift`, GT.4 bands, PF.2/PF.5, `prop:ce-pre-edge`) and the Dirichlet-diagonal machinery it still uses
  (CR.1–4, O.11 diagonal lemmas, PF.2L, PF.T, W.0–W.6); all in the TeX supplement;
- SE.1–SE.5 general de Branges and `PW·PW`;
- Theorem 3.1(c) (tempered distributions);
- fold-tip universality instances;
- `gt:7.10` (owner-deferred);
- the Neumann shell `thm:ce-neumann` (two-sided O(1); its proof is still being moved from notes into the TeX).

**Not a cheap headline.** An "Airy-order `o(d^{1/3})` radius theorem at fixed δ" is not a shortcut: the fixed-δ U.3
route needs a seed with the two-sided fill (e38) that no exhibited seed satisfies, and the honest upper half is O.9′,
i.e. M4.

**Parallelism.** M1 runs alongside M0. M2 and M4 are independent. M3 needs M2 only. With two or three agents the order
is M0 ∥ M1 → M2 ∥ M4 → M3, Headline S → M5 ∥ M6 → M7 → M8.

## 6. Bookkeeping

- QIprojects `docs/lean_status.md`: the Paper I section still describes the `feb41ac` elementary lemmas. Rewrite it after
  M0 with the honest summary of §1: what is proved, and which packages are conditional and on what.
- `THEOREM_MAP.md`: line 741 still says the Theorem B equality case is not formalised (stale); the LobeSaddle "not
  formalised GT.1/GT.1s" notes are stale. Add a pointer to this plan.
