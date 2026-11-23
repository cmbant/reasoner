# Paper I (Fourier sign uncertainty, Cohn–Elkies) — Lean plan

Source: QIprojects `CFT/sign_uncertainty/paper/sign_uncertainty_core.tex` (+ supplement, `CFT/common/`).
Supersedes the "Wave 10–12" plan left after Wave 9 (`7ae7af6`). Audit date 2026-11-23, reasoner `778feac`.

## 1. Where we are

- 64 files, about 64k lines (CohnElkies about 40k, SignUncertainty 14k, TwoEdgeBootstrap 4k, Asymptotics 3k).
  `lake build FormalResearch.SignUncertainty FormalResearch.TwoEdgeBootstrap` passes (9269 jobs, about 9 min). There are no
  `sorry`s or axioms, and the headline theorems use only the standard three axioms.
- **No headline result of Paper I is Lean-checked, not even conditionally on a TeX theorem.** The four introduction
  theorems are `thm:intro-radii` (sign-uncertainty radii plus `gt:7.12` CE radius), `thm:intro-separation` (`gt:7.9c`),
  `thm:intro-hb` (`thm:hb-thresholds`) and `thm:intro-gap` (`thm:ce-shell-gap`).
  - The Hankel problem exists only as an abstract `HankelKernelData` (one witness, `c = 5/2`).
  - `CohnElkiesRadius.ce_radius_airy_order_of_bounds` is only the gluing step. Its hypotheses `hlo` and `hhi` *are* the
    two halves of the theorem, and the module imports none of the Airy or Mellin machinery.
- **Waves 4–9 (about 25k lines) feed only leaves.** About 30 hypothesis packages (`MacroscopicTransferPackage`,
  `GT4CoverageBands`, `PE3OriginData`, `PreEdgeGeneralData`, `AiryTailSymbolSeed`, `MovingDiagFarTail`, `ShellGapPackage`,
  …) have only toy non-vacuity witnesses (all functions 0, constants 1, or degenerate parameters), and none has a real
  instance. `MovingDiagFarTail` has no instance at all. Theorems such as GT.2b, GT.3b, GT.4, PE.3 and `cepe:general` are
  stated for an abstract `fhat` that carries the paper's estimates as hypotheses. Nothing builds `W_S`, `W_D` from `Ai`,
  or `h_mellin` from a CE pair.
- What is genuinely closed and reusable:
  - the Airy base: Theorems D, Q and B with its equality case, Clark two-node, Hermite–Biehler quadrature and
    `at47_*`, and Airy PWS (a)⇔(b);
  - E.1–E.3a (finite dimensions);
  - H.14a and H.14b;
  - the radial rigidity proof `gt:7.5`, modulo compactness;
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
- **Order by sharing.** Do the layer used by the most headlines first. The first milestone is `thm:intro-radii` at one
  level (`gt:7.9` + `gt:7.12`, unconditional); the others reuse most of it.

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

## 5. Milestones (S < 500 lines, M 500–2000, L > 2000; calibration: the Virasoro lower half took about 29k lines)

**M0 Skeleton (S–M).**
- Concrete definitions and the four headline statements, each proved from its input structure.
- Delete or merge the dead packages that the skeleton does not use.
- Rename overclaiming names (`theorem_H14_strict_gap` → `…_core`; `teb_mellin_o1_lower` docstring).

**M1 Classical leaves (parallel; independent of everything else).**
- `hBesselRatio` (DLMF 9.6.2–3; about 0.6–0.8k; route: Bessel ODE for `√z K_{1/3}`, decay, uniqueness).
- `hNicholson` (DLMF 9.11.4; about 0.7–1.1k; third-order ODE `w''' + 4xw' + 2w = 0`, solution span, asymptotics).
- Bessel `J_ν` for real `ν`: bounds and Weber integral DLMF 10.22.43; Laguerre-mode eigen-identity (M–L).
- Radial Fourier transform on `Euc d` for all `d` (M).

**M2 Hankel layer (used by all four headlines; L).**
- Concrete `HankelKernelData` from M1.
- `gt:7.4` (strip reflection, majorant, three lines).
- `lem:radial-compactness` (deep lobe, tail, compactness).
- This discharges the compactness fields of `RadialRigidityPackage` and feeds the H.14 and separation packages.

**M3 Upper O-chain at one level (shared: Hankel upper half and CE upper half; L, technical core).**
- U.1, U.2 (or only the T2 span), U.3, GT.2a, O.3(2), O.4(2)–(3), O.5, O.6, O.11ak (Mellin-lift hub), O.9′ at `m = 1`.
- Highest risk: O.3(2) (V-ray contour deformation, Puiseux) and O.5/O.6. Before starting, look for a shorter TeX
  route to O.3(2).

**M4 Hankel lower half at one level (L).**
- Langer chart `gt:7.7b/c/p` (Rouché exists).
- TE.0 at one level: check whether `teb_quant_c1_typeII` adapts (type I vs type II envelope; open question).
- TE.3 Hankel window and `BandReductionInstance`.
- Discharge the `BootstrapCore/Instance` fields (refactor the Virasoro `ArcBounds`/`QuadratureBounds`).
- L.2/L.6 at one level; chart inversion into `teb_mellin_o1_lower`.

**Headline A, `gt:7.9`:** M2 + M3 + M4 + the Euclidean reduction (BCK/CG, averaging, finite `d` via E.1; M).

**M5 CE upper, Route II at `m₀ = 1` (M–L).**
- CR.4 closure: link `(CR.19)` `Λ_h → cohnS`, expose `Λ`-uniform constants, giving `MovingDiagFarTail`.
- GT.3b with real PF.T and PF2L.2: only the fields Route II uses.
- `thm:ce-post-edge`; `cepe:general` with the real Airy cardinal kernel (`PreEdgeGeneralData.h_saddle`).
- hb-lift assembly (seed mass `m₀ = 1` exists); lift to `Euc d`. This gives `hhi`.

**M6 CE lower (M).** Shell reduction `m = 1`, `O(d)` averaging, and the Hankel lower half from M4 give `hlo`.

**Headline B, `gt:7.12` + `gt:7.12a`, unconditional.** This completes `thm:intro-radii`.

**M7 Separation `gt:7.9c` (M).** Assemble `LangerSignSeparationPackage.langer_approx` from M2 and M4 (gt:7.5,
7.7b/c/p, Montel, slope); `Tneg_asymp` comes from M3/M4.

**M8 Strict gap H.14 (L).**
- Laplace limit L.6 (Stirling and majorants); compactness for `p_c`, `q_c`.
- `o(c^{1/3})` offsets and the infimal `R_d^{CE}` quantification.
- HB–CE.L contributes only its short non-vanishing step.

**M9 All levels (L).**
- TE.0′ and TE.2(4) instance; general `HBSeedSpec` (`gt:1.0pp`); multilevel L.2.
- This gives `thm:intro-hb`, and general `thm:ce-hb-lift` (for the `intro-gap` interpretation).

**Deferred (not on any headline path):**
- Route I (`thm:ce-lift`, GT.4 bands, PF.2/PF.5, `prop:ce-pre-edge`; now in the supplement);
- SE.1–SE.5 general de Branges and `PW·PW`;
- Theorem 3.1(c) (tempered distributions);
- fold-tip universality instances;
- `gt:7.10` (owner-deferred).

**Parallelism.** M1 (4 independent tasks) can run alongside M0. M2 and M3 are independent of each other. M4 needs M2.
M5 needs M1 and M3. With two or three agents, Headline B is the critical path: M0 → M2 ∥ M3 → M4/M5 → M6.

## 6. Bookkeeping

- QIprojects `docs/lean_status.md`: the Paper I section still describes the `feb41ac` elementary lemmas. Rewrite it after
  M0 with the honest summary of §1: what is proved, and which packages are conditional and on what.
- `THEOREM_MAP.md`: line 741 still says the Theorem B equality case is not formalised (stale); the LobeSaddle "not
  formalised GT.1/GT.1s" notes are stale. Add a pointer to this plan.
