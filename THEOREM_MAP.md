# Theorem map and trust boundary

> **Live status — 2026-09-20.** This file is a high-level trust map, not a complete index of every imported module. The authoritative maintained Lean branch is `master`; exact-head hard Lake builds and theorem-local source audits control promotion.
>
> Historical workflow-level green badges from before the repaired hard Lake gates are not verification evidence. Current promoted claims below cite exact module/aggregate runs recorded in `PROJECT_UPDATES/HANDOFF_2026-09-09.md` and QIprojects `docs/lean_status.md`.

## Current maintained baseline

Maintained reasoner head after PR #14:

`29c4d5946f427dfdfd5b9adccca242f0118f6742`.

Latest promoted Lean source verification head:

`df4466a9e5b773db105bb1fcbd14945129d2a33b`.

GitHub Actions run `34390385283` passed placeholder rejection, the three QI-D nested-upper modules and full `lake build FormalResearch` on that exact source tree before merge.

## Status vocabulary

- `FORMALIZED`: Lean source exists.
- `MODULE-GREEN`: the theorem-local hard Lake build passed at an exact source head.
- `AGGREGATE-GREEN`: full `lake build FormalResearch` passed at an exact source head containing the theorem.
- `MERGED`: reviewed source is on `master`.
- `EXTERNAL`: a named mathematical/source premise remains intentionally outside current Lean coverage.

Compilation is not by itself a specification audit. A checked theorem may be narrower than, conditional relative to, or semantically different from the surrounding source theorem.

## Blaschke quartic charge gap

Lean files:

- `FormalResearch/Blaschke/QuarticChargeGapAlgebra.lean`;
- `FormalResearch/Blaschke/QuarticChargeGapReconstructionBridge.lean`.

Current formal core includes the corrected quartic conic/factor algebra, sign chain, squared-gap defect, exact scalar reconstruction prefactor and final unsquaring to the `1/2` gap under explicit reconstruction/analytic hypotheses.

PR #8 hard verification: head `1dc24e93c1483782dd80b162c9b48cd26707fc41`, run `34336956345`, module and full aggregate green; merged.

Status: **FORMALIZED / MODULE-GREEN / AGGREGATE-GREEN / MERGED** for the conditional scalar bridge.

External boundary: raw CAS reconstruction derivation, Bessel/Gram input, Schur-domain theorem, Möbius normalization, residue/Hilbert-metric construction and confluent continuity. Do not describe the complete analytic quartic proof as internally Lean-derived.

## QI-A

The maintained aggregate contains the older four-qubit/chirality/three-copy infrastructure plus the new exact certificate layers:

### Three-copy local-Schur overhead

Lean file: `FormalResearch/QIA/ThreeCopyLocalSchurOverhead.lean`.

PR #9 verification head `2e15ff34467c5de1a2432c6d6bd7c5c7ddad19ed`, run `34339736666`, module and aggregate green; merged.

Lean proves the finite `S3` character identities `6K=L`, `6K=L+3`, and `6K=L+2` in the source regimes.

### Information hierarchy coefficients

Lean file: `FormalResearch/QIA/InformationHierarchyCoefficients.lean`.

PR #10 verification head `3591192788ae917bb43c1f8e7102e95270258efb`, run `34347204321`, aggregate green; merged.

Lean proves the exact scalar coefficient/exponent ordering including `Q_meas,full=21/22` and `xi_meas=log(22/21)`.

External QI-A boundary: operational POVM/recovery/data-processing statements, T07 coding/query architecture, reversible coherent-width Schmidt-number/recovery lower bound and other manuscript-level theorems not represented by these scalar/character modules.

## QI-B

### Symmetric U(1) exponent gap

Lean file: `FormalResearch/QIB/U1InvariantExponentGap.lean`.

PR #11 verification head `297231d4be4780b1d091092a7d841bbbe62edb85`, run `34348733331`, aggregate green; merged.

Source: `QI/invariant_discrimination/paper/invariant_discrimination_exponents.tex` `prop:u1`.

Lean proves the exact scalar factor-two exponent relation for the source family; the twirl/binomial/operational Chernoff derivation remains external.

### B1 apolar kernel (`FormalResearch/QIB1`)

Source: `QI/invariant_discrimination/B1-apolar/results/apolar_finite_defect_results.tex` (`D_F = 3 d_x^2 d_y - d_y^3`), lane record `QI/invariant_discrimination/B1-apolar/notes/STATUS_MATRIX.md`.

Lean proves, for every `d >= 3`, that the monomial-coefficient matrix of `D_F` has full row rank `d-2` over `Q` and `R`, that its kernel has dimension 3, and that over `R` the kernel is spanned by the three coherent powers at `b = 0, +-sqrt 3`. The factorization `lambda_d I - E_d = D_F^dagger R_d D_F`, `R_d > 0` and all finite-defect/Hahn row identities remain external.

### B2 Hamming/Krawtchouk phase algebra (`FormalResearch/QIB2`)

Source: `QI/invariant_discrimination/B2-hamming/results/three_band_hamming_heat_kernel.tex`, section "Exact Hamming/Krawtchouk phase algebra" (`eq:hammingU`).

Lean proves the scalar/Boolean-cube content: Krawtchouk coefficient formula and generating function, the Bose--Mesner eigenaction on a Walsh character, the canonical gate phase `i^|T|` for every Walsh label, and the `choose d m` multiplicity of weight `m`. The two-qubit swap operators, the projectors `E_m` and the operator identity on `(C^4)^(tensor d)` remain external. `Bridges/B2BlaschkeMultiplicityRank.lean` uses `QIB2.card_WalshWeightIndex`.

### B4 late source status

QIprojects now proves the flagship (`thm:flagship` in `QI/invariant_discrimination/paper/invariant_discrimination_exponents.tex`: `F_C = F_K = 1/2`, `xi_inv = log 2`), but the theorem itself is not formalized (QIprojects `docs/lean_status.md` records what the `QIB` modules cover). Any B4 formalization must match a proved source theorem (check `QI/invariant_discrimination/B4-orbit-bergman/notes/CORRECTIONS.md` and `QI/invariant_discrimination/paper/CORRECTIONS.md` first) and keep the class of each statement.

## QI-C

The maintained aggregate contains the finite-field, Gaussian and all-`L` qubit-tail chain, including:

- `FormalResearch/QIC/QubitTailDeterminants.lean`;
- `FormalResearch/QIC/GaussianNonvanishing.lean`;
- `FormalResearch/QIC/QubitTailAllLNonvanishing.lean`;
- Endpoint14/Gaussian endpoint reconstruction modules.

The canonical QI-C all-`m` tail certificate has remained source-stable through the latest audit, and these modules compile in the current aggregate.

Trust boundary: this is the determinant/nonvanishing/certificate layer. The full Jacobian/orbit-identifiability statement behind `d_loc=3` is a separate semantic theorem and must not be inferred merely from aggregate compilation.

## QI-D

### D4 finite doubly-stochastic separation certificate

Lean files:

- `FormalResearch/QID/D4DoublyStochasticCertificate.lean`;
- `FormalResearch/QID/D4DoublyStochasticDualCertificate.lean`.

PR #12 clean verification head `8a95d5ba7fb0b200dfbfb2efb4c97e3710ead8be`, run `34374566836`, both modules and full aggregate green; merged.

Internally checked finite data include `|W(D4)|=192`, orbit sizes `(8,24,8,8)`, witness value `7/6`, Weyl support, exactly `2304` finite coweight constraints with zero violations, and the exact 14-term rational dual.

External boundary: the finite-coweight characterization of semantic `DS(W(D4))` membership and the surrounding generalized-Birkhoff/convex-geometric theorem.

### Nested all-rank lower witness

Lean file: `FormalResearch/QID/NestedLowerWitness.lean`.

PR #13 promoted head `a8d883584eb235fa2f1c4af0c01ec309cedfc0ac`, run `34378799353`, module and aggregate green; merged.

For `n=k+4`, Lean defines the actual block witness and proves `<N_n,A_n>=n+2/3`.

External boundary: generalized-Birkhoff nesting / semantic `A_n in DS(W(D_n))`.

### Nested all-rank upper decomposition

Lean files:

- `FormalResearch/QID/NestedUpperAtomicCore.lean`;
- `FormalResearch/QID/NestedUpperRankOneSums.lean`;
- `FormalResearch/QID/NestedUpperSupportBridge.lean`.

PR #14 module head `15ce8208c11f73b77fc2adbc4ad859f958cd031a`, run `34389943505`; promoted head `df4466a9e5b773db105bb1fcbd14945129d2a33b`, run `34390385283`; all modules and full aggregate green; merged.

Lean proves the exact source identity

`6N_n = 2R_n + 2C_n + sum_a s_a t_a^T`,

its explicit individual row/column rank-one expansion, the four opposite-parity sign atoms and the implication `<N_n,T><=n+2/3` from the individual sharp support bounds.

External boundary: the arbitrary-real type-D rearrangement / determinant-constrained Procrustes theorem supplying those sharp per-atom bounds. Together with the lower-witness boundary above, this is why the complete semantic `DS(W(D_n))` extremal theorem is not yet wholly internal Lean.

### D5 certificate chain

The maintained aggregate imports the D5 rank, enumeration, affine-rank, supporting-facet and full-facet certificate modules. The old theorem-map text saying these pieces were still pending is obsolete. For theorem semantics, consult the source-local QI-D certificate and module statements; aggregate compilation alone does not upgrade their external convex-geometric premises.

## Four-qubit average-entropy maximum (QIprojects PR 193, task T59)

Lean files: `FormalResearch/FourQubitEntropy/*.lean`; the source is
`QI/multiqubit_entanglement/four_qubit_entropy/` (theorems `thm:fqe-moment`, `lem:fqe-purity`, `thm:fqe-entropy-max`).

The development is the Lean companion of QIprojects Paper E (`QI/multiqubit_entanglement/four_qubit_entropy/`) and is developed
here; QIprojects holds no Lean source. Beyond the entropy maximum below it contains the equality case, one-cut rigidity,
the cubic-majorant criterion, Tsallis/Rényi bounds with equality, the HS/cluster crossing, convex-roof ceilings,
`Tradeoff.lean` (the `n = 4` purity–time-reversal tradeoff `π₂ ≥ 1/3 + τ/6`, optimal coefficient, three Bell-pairing zeros of
`F`), and `SevenQubitIcoState.lean` and `SevenQubitIcoPurity.lean` (the seven-qubit icosahedral coefficient tensor of `thm:ico`:
unit norm, maximally mixed one-qubit marginals, the purity polynomial of every three-qubit cut (35) and pair (21)
derived from the tensor, the mean three-body purity `121/917 + (1048/525)(x−37/524)²` on the family with unique minimum at
`x = 37/524`, and the cut and pair purities there; `SevenQubitIcoCert.lean`/`SevenQubitIcoSpectrum.lean`: the spectrum of
every three-qubit cut, `(4α²)⁶,(3α²+β²)²` avoiding the special site and `8α²,(4α²)⁵,(α²+β²)²` containing it;
`SevenQubitIcoEntropy.lean`: the mean three-body entropy of the family is strictly concave with a unique maximiser strictly
between `0` and `37/524`; the pair spectra (`SevenQubitIcoPairSpectrum.lean`) and the enclosure of the maximiser (`star_enclosure`, `star_value`) are formalized in later modules). Kernel `decide +kernel` only; no compiler axiom.

Formalized, with no `sorry`:

- `sexticF_ge`, `sexticF_nonneg` (`MomentInequality.lean`): for every `ψ ∈ (ℂ²)^{⊗4}`,
  `F = 17nP − 12T − 12n³ ≥ (3/4) n W₁ ≥ 0`, with `P`, `T` the summed purities and cubic moments of the
  three `1j` marginals (`Matrix.trace` of the reduced matrices) and `W₁` the squared Pauli expectations. The
  proof is the identity `8F = 6 n W₁ + 3 Σᵢ ‖Vᵢ − 8Uᵢ‖² + 12 Σ_{i<j} ‖(Rᵢ^{(i)} − Rⱼ^{(j)}) z‖²`
  (`sextic_identity`; `Uᵢ = Sᵢ ∏_{j≠i} Lⱼ w`, `Vᵢ = Sᵢ ∏_{j≠i} (Lⱼ + Mⱼ) w`, `w = z ⊗ z ⊗ z̃`, `Rᵢ^{(i)}` the
  one-qubit marginal acting on qubit `i` of `z`; `Generic.lean`), checked as an identity of 32-variable
  polynomials (`Identity.lean`) and transported to all complex states (`Transfer.lean`, `Defect.lean`,
  `Bridge.lean`). `sexticF_ge_sharp` (`Checks.lean`): `3/4` is the best constant (every product state attains
  it). Consequences with the sharp constant: `majorant_stability` (`3 (E_f(M₄) − E_f(ψ)) ≥ (α/2 + a/16) W₁ +
  (α/2) τ`), `entropy_stability` (`3 ln 2 · δ ≥ ((21 − 15 ln 3)/8) W₁ + (15/4 − 3 ln 3) τ`), `tsallis_stability`
  and `e3_sum_le` (`Σ_j e₃(ρ_{1j}) ≤ (6 − P)/36 − W₁/48 ≤ 5/36`). These are the `τ^{3/2}`-free corollaries of the paper's
  estimates; `majorant_stability_of_envelope`, `entropy_stability_of_envelope`, `tsallis_stability_of_envelope`
  (`Stability.lean`) add the paper's term `(a/12)(τ − τ^{3/2})` with `(3/4) W₁ + τ − τ√τ ≤ F` (the weaker consequence of
  `thm:fqe-general-envelope`) as an explicit hypothesis `henv`; `majorant_stability_env`, `entropy_stability_env`,
  `tsallis_stability_env` (`StabilityEnvelope.lean`) discharge `henv` with `envelope_weak`, so these are unconditional.
- Moment defect and distance stability (`PaperEGenDefect.lean`): `sexticQ`, `defectD`, `entropy_gap_ge_defect`
  (`δ ≥ k 𝒟`, `k = (ln 3 − 1)/(2 ln 2) > 16/225`), `entropy_gap_ge_Q`, `majorant_gap_ge_defect`, `tsallis_gap_ge_defect`, and
  `entropy_gap_critical` (`W₁ = 0`: `δ ≥ k (Q + 5τ/2)`) are unconditional. These moment-level estimates take
  the overlap comparison as an explicit argument; the genuine distance `d` (`OD.orbitDist`, `PaperEOrbitDistance.lean`) and
  `thm:fqe-global-overlap` (`GO.globalOverlap_all`, `GOGlue/Final.lean`) discharge it in the `_all` forms
  (`entropy_gap_orbit_stability_dist_all`, `majorant_gap_orbit_all`, `tsallis_gap_orbit_all`, `critical_orbit_sharp_dist_all`).
  `entropy_gap_ge_of_overlap`, `entropy_gap_orbit_stability` (`thm:fqe-orbit-stability`:
  `δ ≥ k ((6+√6)/12) d2 > d2/20`), `entropy_gap_critical_distance` (`eq:fqe-critical-entropy`, constant `(2+√2)/4`),
  `majorant_gap_of_overlap` and `tsallis_gap_of_overlap` (`cor:fqe-orbit-spectral`) are *conditional*: the hypothesis
  `c * d2 ≤ sexticQ ψ` (`d2` standing for `d(ψ)²`) is an explicit argument, never proved or assumed as an axiom.
  For critical states `d2` is the real `dist2` (`CriticalOrbitPhi.lean`) and the hypothesis is discharged except for the
  all-state comparison `Q ≥ 1 - Φ` when `Φ ≥ 1/2`, discharged by `globalOverlap_all`.
- `purity_ge` (`Purity.lean`): `P ≥ n²` from `2P = 2n² + W₁ + τ`, `τ = |ψᵀ ε^{⊗4} ψ|²`.
- `negMulLog_le_hermCubic` (`HermiteBound.lean`): `−x ln x ≤ a x³ + b x² + c x + d` for `x ≥ 0`.
- `meanEntropy_le`, `meanEntropy_M4`, `meanEntropy_M4_max` (`Entropy.lean`, `Attainment.lean`): for a unit
  vector the mean von Neumann entropy of the three `1j` marginals (from `Matrix.IsHermitian.eigenvalues`) is at
  most `1 + log 3 / (2 log 2)`, and `M₄` attains it.

- `meanEntropy_eq_max_iff` (`EqualityMain.lean`): for a unit vector, mean entropy `= 1 + log 3 / (2 log 2)` iff
  `ψ` is a local-unitary image of `M₄` or of `conj M₄`. Forward: equality forces `P = 1` (`EqualityReduction.lean`),
  hence `W₁ = 0` and `ψᵀ ε^{⊗4} ψ = 0`, and the cut-`12` quadratic `(R-1/6)(R-1/2)=0`; `classify`
  (`ClassifyMain.lean`) then normalises `ψ` by explicit local unitaries (magic basis, block form, Euler
  rotations; `Magic`…`Normalize`, `Classify`). Converse: `EqualityConverse.lean`. `LUEquiv` is `∃` unitary
  `a,b,c,d` with `localApply a b c d ψ = φ` (`LocalUnitary.lean`).

- `Checks.lean`: non-vacuity and corollaries. Concrete evaluations of `normSqPsi, P, T, W₁, F` on `|0000⟩`
  (`3, 3, 4, F = 3`), the two-Bell-pair state (`P = 3/2, T = 9/8, W₁ = 0, F = 0`) and the cluster state
  (`P = 1, T = 3/8, W₁ = 0, F = 1/2`); `purity_identity_exact` (`2P = 2n² + W₁ + |ψᵀ ε^{⊗4} ψ|²`, `τ` identified);
  `purity_eq_one_iff` (unit: `P = 1 ↔ W₁ = 0 ∧ ψᵀ ε^{⊗4} ψ = 0`); `sexticF_zero_bloch` (unit and `F = 0` forces
  `W₁ = 0`); `cubicMoment_le_line` (`T ≤ 5/12 + 17/12 (P − 1)`) with `bell2_on_line` (sharp at `(3/2, 9/8)`);
  `tsallis2_le` and `cluster4_tsallis2_max` (mean Tsallis-2 entropy `≤ 2/3`, attained); `M4_invariants`
  (`P = 1, T = 5/12, F = 0, W₁ = 0` for `M₄`); `one_cut_rigidity_12` (unit, `P = 1` and the quadratic on cut
  `12` give `LUEquiv M₄ ψ ∨ LUEquiv (conj M₄) ψ`). `#guard_msgs` pins four of these to the standard axioms.

Trust: the sextic polynomial identity `sexticDefect_check` (`Identity.lean`) is checked by the Lean kernel
alone (`decide +kernel`); the development contains no `native_decide`, and `#print axioms` of `meanEntropy_le`,
`meanEntropy_eq_max_iff`, `sexticF_ge`, `cubicMoment_le_line`, `M4_invariants`, `purity_ge`,
`purity_identity_exact`, `purity_eq_one_iff` and `one_cut_rigidity_12` lists only `propext`, `Classical.choice`
and `Quot.sound`. The identity is split into seven pieces (`F`, `n W₁`, `pairSum`, four residual norms), each
checked against an expanded normal form in its own `IdentityCert*.lean` (generated by
`gen_sextic_certificate.py`; the literals are untrusted data), and the combination is checked in `Identity.lean`.
Machine requirements: kernel memory grows with the number of reduction steps and is not freed within a
declaration, so the whole identity in one declaration needs more than 12 GB (the run was killed there); per
piece it is moderate. Measured on 4 cores and 15 GB RAM (Lean 4.34.0, one `lake env lean` per file, wall time including about 7 s of import
loading; resident size includes the roughly 6.3 GB of memory-mapped `.olean` files that `import Mathlib` plus the
earlier modules already occupy): `IdentityCertF` 26 s / 7.7 GB, `IdentityCertNW` 11 s / 6.6 GB, `IdentityCertPair`
37 s / 8.6 GB, `IdentityCertRes0..3` 34-39 s / 8.3-8.4 GB each, `Identity` 15 s / 7.1 GB. Built through `lake` the group takes about
5 minutes in sequence, and its peak resident size is 8.6 GB, so a machine with 16 GB of RAM is comfortable. The heaviest files of the development are not these: `SevenQubitIcoXSpinZero` (66 s,
10.3 GB) and `PaperECriticalSextic` (93 s, 9.8 GB). The `IdentityCert*.lean` files import one another in a chain so that `lake`
builds them one at a time; removing the chain makes `lake build` run them in parallel, each with its own kernel
memory. The zero-set classification of `F` (`moment_zeros`), one-cut rigidity for cuts
`13` and `14`, the spectral majorant proposition and the Tsallis, Rényi and convex-roof corollaries are
formalized in the later modules named in QIprojects `docs/lean_status.md`, which also lists what is not formalized.

Statement scope against the current paper (`four_qubit_entropy.tex` and its supplement, as of the audit of QIprojects PR 208):

- `prop:fqe-two-flat-rigidity`: the paper states `(TF)` for every unit pure state with an extra term `W₁/4`.
  The first inequality of `(TF)` for every unit state and each of the three cuts is `two_flat_cross_cost_12`,
  `_13`, `_14` (`SpectralSpinFlip.lean`: for an eigenvalue `λ_i ≥ 1/2` of the cut, `W₁/4 + (Σ_{j≠i} λ_j)² - Σ_{j≠i} λ_j²
  ≤ (sum of the other two cut purities) - 1/2`, which is `Δ_k ≥ W₁/4 + 2 e₂`); the second inequality (in terms of the ordered spectrum),
  the equality cases and sharpness are not formalized there (they are
  `two_flat_TF_*`, `two_flat_eq_iff_*`, `two_flat_sharp_*` in `PaperETwoFlatTF*.lean`, and (QF) is `two_flat_QF`). `two_flat_rigidity` is the critical specialization
  `W₁ = 0`; the Schmidt-rank-two consequence `two_flat_rank` holds for every unit state.
- `lem:seven-entropy-linear-purity`: proved with the sharp slope, `3 - S ≥ (7 log₂ 7/48)(8 tr ρ² - 1) ≥ (49/120)(8 tr ρ² - 1)
  ≥ (2/5)(8 tr ρ² - 1)` (`LinPur.entropy_linear_purity_sharp_nats`, `_rat_nats`, `entropy_linear_purity_nats`), now
  corollaries of the all-dimension slope and its equality case (section on the entropy–purity slope below). The competitor band and the
  eigenvalue cap `497/1000` use the slope `2/5`.
- `lem:seven-joint-scalar-majorant` (AH-6) holds in the paper on all of `[0,∞)²`; it is proved in branch `paper-e-ah6` for the
  explicit coefficients (`AH6.joint_scalar_majorant`, see "Branch `paper-e-ah6`" below). `meanEntropy3_le_jointP5_unit` gives
  `E₃ ≤ 𝒫₅` for every unit vector under `ScalarMajorant (polyH K h) 1`; the `497/1000` versions are weaker consequences.
- `prop:stab7`: the lower bound `π₃ ≥ 19/140` is proved for every seven-qubit stabilizer state (`SevenQubitStabilizer.stab7`,
  `stab7_ne_ico`), following the paper's analytic proof: `pi3_identity` and `shadow_identity` (the two identities, from
  `meanPurity_eq_lin`, complementarity and `Σ A_j = 2^7`) and integrality of `A_j` and `S_1` for stabilizer states
  (`NQubit/Shadow/Stabilizer`: `IsStabilizerState`, `weightEnum_nat`, `shadowCoeff_nat`, via the character
  `φ_t(PQ) = φ_t(P) φ_t(Q)` on commuting words). A stabilizer state here is `nsq ψ = 1` with a group of `2^n` commuting
  Pauli words (closed under letterwise product) having `⟨P⟩² = 1`. Axioms `[propext, Classical.choice, Quot.sound]`.
  Sharpness: `SevenQubitStabilizerSharp` (`stab7_sharp : IsLeast {x | ∃ ψ, IsStabilizerState ψ ∧ meanPurity ψ 3 = x} (19/140)`):
  the witness graph `0x00cf17` of `SevenQubitStab7` is given by seven bitmask rows `adjW` (`adjW_spec` links them to the
  `21`-bit encoding), `rankSumW` (`Σ_{|S|=3} 2^{3-rk_2} = 38`, `decide +kernel` on `graphCutRankBits`) and
  `meanRdmPurity_graphStateNorm` give `meanPurity_graphW : π₃ = 19/140` for the library's `graphStateNorm`, which is a
  stabilizer state by `NQubit/Graph/Stabilizer` (`graphStateNorm_isStabilizerState`, `isStabilizerState_graphW`).
  Axioms `[propext, Classical.choice, Quot.sound]`. `SevenQubitStab7`'s `pi3_witness` (recalled formula) is no longer needed
  for sharpness.
- `prop:rains-faces` (`n = 7, 13, 19, 20`), for every unit vector, not only stabilizer states (`SevenQubitRainsEquality`): the Rains bound
  `L_n ≤ π_{⌊n/2⌋}` (`rains_bound_<n>`, exact dual certificates `es<n>`, `ys<n>` checked by `decide +kernel`; `L_n = 1/8, 25/1408,
  93/38896, 1193/739024`); a state attaining it has the unique Pauli weight distribution `tgtL<n>` and shadow distribution `sh<n>`
  (`rains_equality_profile_<n>`, `rains_equality_shadow_<n>`), because the certificates are strictly complementary on the listed
  zero weights and zero shadow coefficients (`lp_slack`, `lp_equality_zero`, `faceR_of_equality`) and the face has one point
  (`faceR_unique_of_data`, the integer left inverses of `SevenQubitRainsFaces`). For `n = 7, 13` the profile has `S_1 = 7/4`,
  `S_3 = 39/4`, so **no stabilizer state attains the bound** (`stabilizer_ne_rains_7`, `stabilizer_ne_rains_13`). Not covered:
  existence of a state with these profiles, and the `n = 20` Type I additive `F₄` code reading. Axioms
  `[propext, Classical.choice, Quot.sound]`.
- `prop:shadow-complement` (`SevenQubitShadowComplement.lean`, with `SevenQubitShadowComplementModel.lean` and
  `SevenQubitShadowComplementPauli.lean`): for every (not necessarily normalized) `ψ : Ψ (m+1)` with `m` even and every
  distinguished qubit `s`, `odd_weight_identities` proves both boxed identities, `∑_{j odd} B_j = 2^m/2 · tr ρ_s² - 2^m/4 · q_s`
  and `2^m ‖ρ̄ - Jρ̄J⁻¹‖₂² = 4 ∑_{j odd} B_j`, with no hypothesis other than `Even m` (`B_j = weightEnumExcl ψ s j`,
  `tr ρ_s² = cutPurity ψ {s}`, `q_s = shadowQ (spinFlipOp (univ.erase s)) (branchVec ψ s)`, `‖A‖₂² = hsNormSq A = Re tr(A†A)`,
  `J = spinFlipOp = ε^{⊗m} K`, `ρ̄ = rho (branchVec ψ s)` whose matrix is the library's `rdm` (`rho_branchVec_single`, `rdm_eq_sum`); `weightEnumExcl_eq_sum_trace_sq`:
  `B_j = ∑_{wt P = j} (tr ρ̄ P)²` via `trace_rdm_pauli`). The Pauli
  expansions are discharged from `Reduced/Purity` and `TimeReversal/OddOverlap`: `two_pow_mul_cutPurity_erase`
  (`2^m tr ρ̄² = ∑ B_j`), `two_pow_mul_sum_Tm` (`2^m tr(ρ̄ J ρ̄ J⁻¹) = ∑ (-1)^j B_j`, via `Rspin_eq` and `two_pow_mul_Rspin`),
  `cutPurity_erase` (`tr ρ̄² = tr ρ_s²`), `isSpinFlip_spinFlipOp`; the abstract model gives `shadowQ_eq` (`q_s = 2‖T‖_F²`),
  `shadowQ_eq_trace` (`q_s = 2 tr(ρ̄ J ρ̄ J⁻¹)`) and `hsNormSq_rho_sub_rhoFlip`. `odd_weight_takagi` (`shadowQ_takagi`,
  `takagi_frobenius`): for `tr ρ_s² = 1/2` and a Takagi factorization `T̂ = U diag(t) Uᵀ` of `T̂ = 2T`, `q_s = (t₁² + t₂²)/2` and
  `∑_{j odd} B_j = 2^m/4 (1 - (t₁² + t₂²)/2)`. Axioms `[propext, Classical.choice, Quot.sound]`. Not formalized: existence of the
  Takagi factorization and the basis independence of the `t_i`; the distinguished qubit enters as an arbitrary `s : Fin (m+1)`.
- `SevenQubitIcoContraction` and `SevenQubitIcoContractGram` (`esG1_*`, `esG2_contain`) are not paper statements: the paper
  proves `prop:entropy-seven-stationarity` from `lem:seven-family-symmetric-criticality` (not formalized) and no longer
  displays these identities.
- `prop:fqe-spectral-spinflip` (`SpectralSpinFlip.lean`): `spectral_spinflip_12`, `_13`, `_14` give, for every unit four-qubit
  state and every eigenvalue `λ` of the cut marginal `red12 ψ`, `red13 ψ`, `red14 ψ`, `(max (2λ - 1) 0)² ≤ τ + W₁/2` with
  `τ = normSq (spinFlipForm ψ)`; `spectral_spinflip_12_purity` etc. restate the right side as `2 (P - 1) - W₁/2` (`spectral_rhs_eq`,
  from `purity_identity_exact`), hence `≤ 2 (P - 1)`; `eigenvalues_le_half_of_purity_one` (`P = 1` forces every balanced
  eigenvalue `≤ 1/2`); `spectral_spinflip_coeff_optimal`: the coefficients `1` of `τ` and `1/2` of `W₁` cannot be lowered
  (tested on `bell2` and on `|00⟩ ⊗ χ`, `χ` maximally entangled). Pure unit states only.
- `lem:fqe-isospectral-overlap` (`IsospectralOverlap.lean`): `isospectral_overlap` proves the lemma for equal local dimensions
  (`M W : Matrix ι ι ℂ`, common Schmidt coefficients expressed as `W W† = P (M M†) P†`, `W† W = Q (M† M) Q†` with unitary `P`, `Q`,
  i.e. unrelated Schmidt bases), for every eigenvalue `l` of `M M†` in place of `λ₁` (for `l > 1/2` it is the largest one, and for
  `l ≤ 1/2` the right side is `0`); `antiunitary_overlap` is the instance `W = E M̄ F`. The proof uses Birkhoff's theorem
  (`rearr_ds`). Not formalized: unequal local dimensions (zero padding) and the attainment statement (sign-flipped Schmidt terms),
  and the general two-parameter sharpness family of the proposition.
- Not formalized, new in the current paper: `lem:seven-family-symmetric-criticality` and the exact transverse Hessian floor
  `(350 - 6√2005)/4585` of `thm:icolocal` (`prop:seven-resolvent-majorant` and `cor:seven-resolvent-matrix` are not Paper E
  statements; the positive-kernel proof of AH-6 is formalized).

### Branch `paper-e-lean2`: flip gradient, general and critical envelope

New modules (all `FormalResearch/FourQubitEntropy/`, imported by `FormalResearch.lean`; kernel `decide +kernel` and
`ring`/`linarith` only, no `sorry`, no `native_decide`, no new axioms; `#print axioms` of every headline theorem below is
`[propext, Classical.choice, Quot.sound]`).

- `thm:fqe-general-envelope` (`GeneralEnvelope.lean`, `general_envelope_unit`): for every unit `ψ`,
  `F ≥ (3/4 + 7τ/(8(1+√τ))) W₁ + τ − τ√τ`, `τ = |s|²`; `envelope_weak` is the `W₁ ≥ 0` consequence
  `F ≥ (3/4) W₁ + τ − τ√τ`; `prop:fqe-critical-envelope` is `critical_envelope` (`W₁ = 0`: `F ≥ τ − τ^{3/2}`).
  Proof: the sextic identity (S) (`Identity.lean`) gives `96F − 72 n W₁ = Σᵢ ‖Rᵢ‖² + 144 (pair part)` (`FlipSos.lean`,
  `flip_sos`); along the spin-flip pencil `xr φ ρ = φ + ρ φ̃` (`φ` flip-orthogonal, `N = 1+ρ²`, `s = 2ρ`,
  `W₁ = (1−ρ²)² W₀`) the flip gradient (FG, `lem:fqe-flip-gradient`) gives `(1−ρ²) h' = D − 6ρ h`, with `D ≥ 0`, and the
  monotone integration (`calM_mono`, `envelope_pencil`) transports the `s = 0` bound of `thm:fqe-moment` to `s ≠ 0`.
  Differences from the paper: no permanent/`Θ` proof is used for the critical case (it is the `W₁ = 0` corollary of the general
  one); the phase normalisation uses `IsAlgClosed` square roots and the case `|s| = 1` (flip-invariant state, `W₁ = 0`) is
  treated separately (`blochSq_eq_zero_of_spin_one`).
- `lem:fqe-flip-gradient` (`FlipGradientReal.lean`, `flipGradient`; `FlipGradient.lean`, `flipGradDefect_zero`): 
  `d/ds Hval(ψ + s ψ̃)|₀ = (1/4) Re ΣᵢYᵢ + Re s (16 n² + 14 W₁ − 16 |s|²)` with `Hval = 4F − 3 n W₁`. The identity is the
  polarisation (dual numbers `Dual ℂ`, `DualJet.lean`, `hasDerivAt_generic`) of the sextic form: `8 · H4dual z w = Rg z w + Rg w z`
  for all complex `z, w`, a polynomial identity in 32 variables checked by the kernel in pieces (SparsePoly, prime keys;
  generator `gen_flipgrad_certificate.py`): blocks `N, P, W` (`FlipGradientCertSmall`),
  `T12, T13, T14` (a- and b-parts), `Ysite0` per site and swapped (`FlipGradientCertY0..3`, `Ys0..3`), the spin part
  `S`, `Ss` (`FlipGradientCertS`, `Ss`), assembled in `FlipGradient.lean`. Statement here is a derivative of `Hval` along the
  real pencil (the paper's complex-polarised form is its `Re` part).
- `StabilityEnvelope.lean`: `majorant_stability_env`, `entropy_stability_env`, `tsallis_stability_env` are the stability theorems of
  `Stability.lean` with the envelope hypothesis `henv` discharged; the HS-overlap hypothesis (`thm:fqe-global-overlap`) is untouched.
- `EnvelopeEquality.lean`: `critical_envelope_attained`: for every `κ ∈ [0,1]` the state `G(a, ib, ib, ib)`,
  `a² = (1+κ)/2`, `b² = (1−κ)/6`, is a unit critical vector with `|s| = κ` and `F = τ − τ^{3/2}` (`Zsum = 6 b² (a² − 3b²)²`), so the
  critical envelope is sharp for every `τ`; `envelope_eq_forces_critical`: `F = τ − τ^{3/2}` for a unit vector forces `W₁ = 0`.
  The full equality classification is in branch `paper-e-envelope-equality` (below).
- `E3Converse.lean`, `e3_sum_eq_iff`: for unit `ψ`, `Σ_j e₃(ρ_{1j}) = 5/36` iff `ψ` is LU equivalent to `M₄` or its conjugate.
- `PaperECriticalRenyiEq.lean`: `renyi_grouping_eq_iff` (`0<a<1`: equality iff `a = 1/2` and `H(u) = H(v)`),
  `renyi_binary_eq_iff` (`a ∈ {0, 1/2, 1}`), `renyi_cubic_eq_iff` (the cubic bound is attained iff the spectrum is pure or uniform on
  its support, `PureOrUniform`), with `Jf_pos` strictness and `log_add_eq_iff`.

Machine requirements (4 cores, 15 GB RAM, `lake build` one module at a time; wall time and peak resident size, which includes
about 6.3 GB of memory-mapped `.olean` files): `FlipGradientCertSmall` 20 s / 6.6 GB; `FlipGradientCertT12`, `T13`, `T14`
61-63 s / 8.2-8.3 GB each; `FlipGradientCertY0..3`, `Ys0..3` 37-41 s / 7.5-7.6 GB each; `CertS` 21 s / 6.6 GB; `CertSs` 24 s /
6.6 GB; `FlipGradient` 45 s / 8.5 GB; `FlipPsi` 27 s, `FlipSos` 16 s, `GeneralEnvelope` 25 s, `StabilityEnvelope` 14 s,
`EnvelopeEquality` 15 s, `E3Converse` 16 s, `PaperECriticalRenyiEq` 23 s (each about 6.5 GB). Unsplit versions were measured and
rejected: the whole dual-number `F` identity needs 12.1 GB / 146 s, and the unsplit `Ysum` 11 GB. The `FlipGradientCert*` files import
one another in a chain so that `lake` builds them one at a time. Negative test: changing one coefficient
`576 → 577` in `FlipGradientCertS.lean` makes `decide` fail (restored afterwards).

Not done in this branch, with the obstruction:
- `lem:seven-joint-scalar-majorant` (AH-6): formalized in branch `paper-e-ah6` (below).
- Equality cases of `thm:fqe-general-envelope` / `prop:fqe-critical-envelope` and the second inequality of `(TF)`: done in
  branch `paper-e-envelope-equality` (below).
- `prop:stab7` identities (Pauli/shadow enumerators): not attempted in this branch; formalised later (see `prop:stab7` above).

## Fully-PPT three-qubit GME (QIprojects PPT THREE QUBIT paper, lane T57)

Lean files: `FormalResearch/PPTThreeQubit/*.lean`, aggregate `FormalResearch/PPTThreeQubit.lean`; the source is
`QI/hidden_entanglement/ppt_three_qubit/fully_ppt_three_qubit_gme.tex`. Biseparability is the
finite-decomposition definition (a sum of rank-one projectors onto vectors that are products across some cut); GME is its
negation. All headlines depend only on `[propext, Classical.choice, Quot.sound]` (pinned `#print axioms` guards); no
`native_decide`. `CoexistencePPTData.lean` is generated by `gen_coex_ppt.py` (exact Q(omega) arithmetic, checked by
`decide +kernel`).

| paper label | declarations | notes |
|---|---|---|
| `prop:ppt3-witness` | `prodA_classification`, `prodA_of_qs`, `prodA_of_v`, `formH_qs`, `formH_nonneg_of_cutProduct` | every `s > 0`, all three cuts |
| support argument (proof of GME) | `trace_Hs_nonneg_of_biseparable`, `trace_nonneg_of_biseparable` | any supported form nonnegative on cut products |
| `thm:ppt3-family` | `ppt3_family_ppt_iff`, `ppt3_family_ppt_gme`, `ppt3_family_gme`, `tInterval_order`, `ppt3_family_explicit_member_ppt` | exact PPT window `[t_-, t_+]` (both directions) and GME; rank five and the rank profiles `(5,8,8,8)` / `(5,7,7,7)` are in `RankProfile.lean` (next rows); minimality of rank five (low-rank PPT theorem) not formalised |
| `thm:ppt3-phase-coexistence` | `ppt3_phase_coexistence`, `ppt3_phase_coexistence_full`, `sigmaBS_strict_ppt` | explicit biseparable decomposition; strict PPT (`T_c >= I/400`); rank five not stated |
| `prop:ppt3-exposed-transition` | `ppt3_exposed_state`, `ppt3_exposed_transition`, `ppt3_exposed_transition_full`, `exposed_line_fully_ppt` | `sigma_D^{T_c} >= I/300`; whole line `>= I/400` by convexity (stronger than the paper's `I/1200`) |
| `lem:ppt3-h0` | `formH0_qs_identity`, `formH0_nonneg_of_cutProduct`, `trace_H0_nonneg_of_biseparable` | |
| `thm:ppt3-orbit` (b), PPT and GME | `rhoSurface_filter`, `ppt3_orbit_ppt`, `ppt3_orbit_gme`, `ppt3_orbit_ppt_gme` | every `1/sqrt 3 < tau < 1`, `a > 0`; rank profile in `RankProfile.lean` (next rows); part (c) not formalised |
| `cor:ppt3-extreme5` (PPT, GME) | `sigma5_eq_member`, `sigma5_gme`, `sigma5_ppt_gme` | extremality of the single point `σ`: see `cor:ppt3-extreme5` (extremality) below; the parametric extremality and the level-two noise bound are not formalised |
| flat states fully PPT (`sec:ppt3-flat`) | `Flat.flat_form`, `Flat.flat_pt_conj`, `Flat.flat_fully_ppt` | flatness defined by maximally mixed marginals |
| local filters preserve biseparability | `isBiseparable_conj_localDiag_iff`, `isBiseparable_smul_pos` | diagonal product filters |
| `lem:ppt3-product-kernel` | `ppt_product_kernel`, `kernel_free_of_gme` (via `decomp_of_cut_kernel`, `biseparable_of_prodA/B/C_kernel`) | unconditional, axioms `[propext, Classical.choice, Quot.sound]`. The 2⊗3 input (Horodecki: PPT on `ℂ²⊗ℂ³` is separable; not in Mathlib) is `pptSeparable23` (`PPTSeparable23.lean`), transported from the vendored math-lab proof `ChainPPT.pptSeparable23` (`ThirdParty/math-lab/NOTICE.md`). Arbitrary nonzero product kernel vector `a⊗b` on `ℂ²⊗ℂ⁴`; local invertible congruences replace the paper's local unitaries |
| `[GIM]` supported-face criterion (proofs of `cor:ppt3-extreme6`, `cor:ppt3-extreme5`, `thm:ppt3-orbit` extremality) | `MatrixAnalysis.ExtremeCriterion.mem_extremePoints_of_faceDirection` (face directions multiples of `σ` ⇒ extreme), `MatrixAnalysis.ExtremeCriterion.eq_smul_of_isFaceDirection` and `MatrixAnalysis.ExtremeCriterion.mem_extremePoints_iff_faceDirection` (converse), `MatrixAnalysis.ExtremeCriterion.exists_posSemidef_add_smul` (perturbation `σ ± εD` stays in the cone), `MatrixAnalysis.ExtremeCriterion.exists_sandwich_of_ker`, `MatrixAnalysis.ExtremeCriterion.mem_extremePoints_of_sandwich` (`σ = B X B†`, `B` injective, nullspace of the kernel-vector system is `span X`), `ppt3_extreme_iff`, `ppt3_extreme_of_sandwich` | generic over a finite index type and finitely many real-linear cut maps `T c` (`MatrixAnalysis/ExtremeCriterion.lean`; `fullyPPT T` = unit-trace PSD with all `T c ρ` PSD, Mathlib `Set.extremePoints ℝ`); three-qubit specialisation uses `ptA/ptB/ptC` (`cutPT`, `fullyPPT3`, `mem_fullyPPT3_iff`). The converse needs each `T c` to preserve Hermiticity (proved for the partial transposes, `cutPT_isHermitian`). The paper's rank computations (rank 24 over `Q(√17, i√3)` / sector minors) are *not* formalised: this is the criterion only; the `B Y B†` form lets a Lean-checked linear-algebra certificate be plugged in via `hnull` |
| `cor:ppt3-extreme5` (the rational member `σ` of `eq:ppt3-sigma5` is an extreme fully-PPT state) | `sigma5_extreme` (via `ppt3_extreme_of_sandwich`), `sigma5_null`, `face_solve`, `hrow_of`, `rowEq`, `kernel_sigma5`, `Bs_injective`, `trace_sigma5`; data `cert`, `kernel_check` (in `SigmaExtremeData.lean`); algebra `coefD` (in `SigmaExtremeAlg.lean`), `mulVec_ptG_sandwich`, `coefD_map` | `SigmaExtreme.lean`, `SigmaExtremeData.lean`, `SigmaExtremeAlg.lean`; axioms `[propext, Classical.choice, Quot.sound]`. Single point `τ = 48/55`, `Q = 11/5` only. The 24 row equations (three kernel vectors per cut, direct and adjoint rows from Hermiticity) are solved by an exact certificate `Λ` over `ℚ(ω)` (`QuadraticAlgebra ℚ (-1) (-1)`, `decide +kernel`) mapped to `ℂ` by `φω`; the kernel vectors are checked to lie in `ker σ^{T_c}` by `kernel_check`. The parametric all-`Q` extremality (paper's 2×4 low-rank theorem) and `cor:ppt3-extreme6` are not formalised |
| `eq:ppt3-asymmetry-upper`, `eq:ppt3-pinch` (trace-distance bounds of `cor:ppt3-symmetrisation`); `eq:ppt3-dist-lift` and the scalar core of `eq:ppt3-lambda` (`prop:ppt3-kernel-quant`) | `bsDist_le_permAvg` (`D(ρ,BS) ≤ ½‖ρ - 𝒮(ρ)‖₁`), `bsDist_le_swap_average` (`D(ρ,BS) ≤ ¼‖ρ - S_BC ρ S_BC‖₁`, PPT at `A|BC`), `distance_lower_bound` (witness bound `g/(2L+Λ) ≤ ½‖ρ-σ‖₁`), `kernel_lift_distance` (`eq:ppt3-dist-lift` for `W = W₀ + λK†K`), `kernel_quant_core`, `kernel_quant_form` (conditional quadratic form of `prop:ppt3-kernel-quant`, abstract `Ω`, `M`), `bsDist_le_cyclic` (cyclic `ρ`, transpositions `S_AC`, `S_AB`); infrastructure `traceDist`, `bsDist`, `bsDist_le`, `le_bsDist`, `exists_biseparable_state`, `tnorm_real_smul`, `trace_permAvg` | `PPTThreeQubit/TraceDistance.lean`, `Pinching.lean`, `KernelQuantCuts.lean`; the generic parts (`tnorm`, `tnormG`, `tnorm_real_smul`, `distance_lower_bound`, `kernel_lift_distance`, `kernel_quant_core`, `kernel_quant_form`, `kernel_quant_matrix`) are in `MatrixAnalysis/{TraceNorm,TraceNormGeneral,TraceDistance,KernelQuant}.lean`; axioms `[propext, Classical.choice, Quot.sound]`. The trace norm is `MatrixAnalysis.tnorm` (Hermitian matrices); `bsDist` is the infimum over unit-trace biseparable states. `eq:ppt3-pinch` in the paper's form is `bsDist_le_tnormG_P3P1` (in `Pinching.lean`) (`D(ρ,BS) ≤ ‖P₃ρP₁‖₁`, with `tnormG X = sup {Re tr(UX) : U†U ≤ 1}`, `tnorm_le_two_tnormG`, `pinch_offdiag`: `P₃ρP₁ + P₁ρP₃ = (ρ - S_BC ρ S_BC)/2`); the Hermitian form is `bsDist_le_swap_average`. `prop:ppt3-kernel-quant` for the cut-product vectors: `MatrixAnalysis.kernel_quant_matrix` (isometric embedding `J`, `λ = (L+L²/α)/μ`), `cutEmb` (in `KernelQuantCuts.lean`) (`b ↦ U_c†(a⊗b)`), `cutEmb_isometry`, `exists_cutEmb`, `kernel_quant_cutProduct` (`W = W₀ + λKᴴK ≥ 0` on every cut-product vector), `kernel_quant_distance` (`D(ρ,BS) ≥ g/(2L+λβ)`), `psd_of_bound`. Hypotheses are those of the paper, uniform in `c` and unit `a`: `‖W₀‖∞ ≤ L` as `|⟨p,W₀q⟩| ≤ L‖p‖‖q‖`, `Ω ≥ α` on `ker M`, `‖Mv‖² ≥ μ‖v‖²` on `(ker M)^⊥` (stated for `M = K ∘ cutEmb c a`). Only `rem:ppt3-hand-radius` (explicit constants for the family, exact minors) is not formalised |
| `cor:ppt3-chirality` (b) (intrinsic local chirality of `R_s`) | `det_phiS` (`det φ_s(z) = -3(z²+s)²`), `Bs_qs_eq`, `fullProd_mem_Rs`, `fullProd_mem_Rs_iff`, `tri_mem_Rs_of_ptS` (exactly three fully product rays `[|1⟩³]`, `[(|0⟩±i√s|1⟩)³]`), `fullProd_mem_Rsbar`, `eq_smul_one_of_eigen`, `eq_smul_of_agree` (Möbius map fixed by three points), `filter_key`, `filter_proportional`, `shiftVec_eVec`, `eq_zero_of_shift_eigen_Rsbar` (no `ω²`-eigenvector of the cyclic shift in `conj(R_s)`), `no_local_filter_conj` (no invertible local filter maps `R_s` into `conj(R_s)`), `no_local_filter_conj_onto`, `no_local_filter_state` (no state with range `R_s` is `F ρ̄ F†`), `stabiliser_iff`, `exists_mobius`, `exists_filter_perm`, `eq_smul_of_perm` | `Chirality*.lean`. Filters are `locMat FA FB FC` with `IsUnit` determinants, `Rs s = ran B_s`, `Rsbar s` its conjugate (`star y ∈ Rs s`). Stronger than the paper's statement: into rather than onto. The stabiliser statement is `stabiliser_iff` (a filter stabilises `R_s` iff `F_B, F_C ∝ F_A` and `F_A` permutes the three points) plus existence/uniqueness of the Möbius map of each of the six permutations; the abstract group isomorphism with `S₃` is not formalised. Part (a) is in `ChiralityUnitary.lean` (next row) |
| `cor:ppt3-chirality` (a) (local unitaries and `ρ_t`, `ρ̄_t`) | `range_rhoT` (`ran ρ_t = R_1` for every `t > 0`), `ppt3_chirality_conj` (`ρ_t ≠ U ρ̄_t U†` for every local unitary `U = U_A ⊗ U_B ⊗ U_C`), `timeReverse`, `ppt3_chirality_timeReverse` (same for the spin time reversal `Y^{⊗3} ρ̄ Y^{⊗3†}`), `ppt3_chirality_window` (on `[t_-, t_+]`: fully PPT, GME and both chirality statements) | `ChiralityUnitary.lean`. Different route from the paper: (a) is derived from the filter-level `no_local_filter_state` via `ran ρ_t = R_1`, so it holds for all `t > 0` rather than `t > 3`; the paper's eigenvalue/nondegenerate-ray argument is not formalised |
| `thm:ppt3-family` rank claims, `thm:ppt3-orbit` rank profile, `cor:ppt3-extreme5`/`cor:ppt3-extreme6` rank profiles | `rankProfile` (`(rank ρ, rank ρ^{T_A}, rank ρ^{T_B}, rank ρ^{T_C})`, `Matrix.rank` over ℂ), `rank_rhoT` (`rank ρ_t = 5`, `t > 0`), `rankProfile_rhoT_interior` (`(5,8,8,8)` for `t_- < t < t_+`), `rankProfile_rhoT_ten_thirds`, `rankProfile_rhoT_tMinus`, `rankProfile_rhoT_tPlus` (`(5,7,7,7)`), `rankProfile_rhoSurface` (`(5,5,5,5)`, every `1/√3 < τ < 1`, `a > 0`), `rankProfile_sigma5`, `sigma6` (`eq:ppt3-sigma6`, `a = t_-`, `b = 8(9-a)/5`), `rankProfile_sigma6` (`(5,6,6,6)`); general lemmas `rank_sandwich_of_leftInv` (`rank (B X B†) = rank X` for `B` with a left inverse), `rank_factor_diag` (`rank (L D L†) = #{k | d_k ≠ 0}`), `rank_ptB_eq_ptA`, `rank_ptC_eq_ptA` | `RankProfile.lean`. Ranks are those of the unnormalised operators of the library. The `LDL*` factors of `FamilyPPTFactor.lean`/`SurfacePPTFactor.lean` are unit lower triangular in a row order (`det_Lt_rows`, `det_Lq_rows`), so the ranks are the numbers of nonzero pivots (`rank_ptA_rhoT`, `rank_ptA_rhoQ`, `ptA_sigma6_eq_mul`). Kernel dimension at a cut is `8 - rank`. The paper's profile of `σ_6` is stated for the PPT state; PPT and extremality of `σ_6` are not formalised (only the ranks). The paper writes profile `(5,6,6,6)` for `σ_6` and `(5,8,8,8)` for the interior of the window. Minimality of rank five (low-rank PPT theorem) not formalised |
| `thm:ppt3-w-class` (mixed `W` class; every constructed state) | `hyperdet` (Cayley's hyperdeterminant, `c_{abc} = x(4a+2b+c)`), `IsWClass` (cone: finite nonnegative combinations of `|φ⟩⟨φ|` with `Det φ = 0`), `IsWClass.add`, `IsWClass.smul`, `IsWClass.sum`, `IsBiseparable.isWClass`, `IsWClass.mix` (mixtures with biseparable noise), `IsWClass.filterDiag` (diagonal local filters); atoms `isWClass_u_e` (`[u]+[e]`), `isWClass_u_v` (`[u]+4[v]`), `isWClass_u_wv` (`[u]+[w-v]`), `isWClass_v_bw` (`[v+bw]+b²[o]`), `hyperdet_u_add_e` (`4(z³-1)`), `hyperdet_u_add_v` (`z²-4`); decompositions `isWClass_wForm_diag`, `isWClass_wForm_nonpos`, `isWClass_wForm_pos`; states `isWClass_rhoT` (`0 < t ≤ 12`), `isWClass_rhoT_window`, `isWClass_sigma6`, `isWClass_rhoQ`, `isWClass_rhoSurface` (`1/√3 < τ < 1`, `a > 0`), `isWClass_sigma5`, `isWClass_sigmaLine` (`-1/200 ≤ t ≤ 1`), `ppt3_w_class`; the full-rank state: `rhoTilde` (`eq:ppt3-tilde-rho`, defined here), `isWClass_A1`, `isWClass_A2` (`eq:ppt3-w-atoms`, first and last lines), `det_A2`, `isWClass_rhoTilde` | `WClass.lean`, `WClassStates.lean`, `WClassTilde.lean`. Lean states membership of the unnormalised operators in the cone over `𝒲`, i.e. of the normalised state in `𝒲` (the paper's convex hull of pure zero-three-tangle states). The decompositions are those of the proof (diagonal case with `A ≤ E+V/4`; surface with `E ≥ 1` via `[v+bw]+b²[o]`, `E < 1` via `μ([u]+[w-v])`; the line at `t = -1/200` via `μ = 10930399/348000000`), the surface inequalities proved in the coordinate `Q` (`qO_mul_qV_sub` is `OV-G²=2E-1`). `ρ_t` is in the class for all `0 < t ≤ 12`. `ρ̃` is only defined and shown to be in the class: that it is fully PPT and GME (`cor:ppt3-robust`, witness and trace-norm data) is not formalised. Not formalised: general (non-diagonal) local filters (hyperdeterminant scaling by the squared product of local determinants); the remark on the interior of `𝒲` among fully-PPT GME states |
| `cor:ppt3-symmetrisation` (a), (b) biseparability, (c) separability part | `isSeparable_of_swap` (PPT + invariant under the swap of the two qubits of `ℂ⁴` ⇒ separable on `ℂ² ⊗ ℂ⁴`, via `sep_of_supported`/`pptSeparable23` on the triplet block and a positive operator on the singlet block), `isBiseparable_of_cut_separable`, `isBiseparable_of_swapBC`, `isBiseparable_of_swapAC`, `isBiseparable_of_swapAB`, `no_gme_of_swap_invariant`, `isBiseparable_swap_average`, `permAvg`, `isBiseparable_permAvg` | `SwapSymmetric.lean`. Swaps are `swapBC/swapAC/swapAB : Fin 8 → Fin 8` acting on indices; `ρ` invariant means `ρ (σ i) (σ j) = ρ i j`. `isBiseparable_swap_average`: `(1/2)(ρ + S ρ S)` for any `ρ ≥ 0` PPT at `A|BC` (equals the `P₃, P₁` pinching; the identification is not formalised). Not formalised: separability of `𝒮(ρ)` across each cut separately (only biseparability), and the identification of the swap average with the pinching `P₃ρP₃ + P₁ρP₁` (only `P₃ρP₁ + h.c. = (ρ - S_BC ρ S_BC)/2` is proved, `pinch_offdiag`); the trace-distance bounds `eq:ppt3-asymmetry-upper`, `eq:ppt3-pinch` are in the trace-distance row above |
| `lem:ppt3-kernel-penalty` (kernel-penalty witness lift) | `exists_kernel_penalty` (compact `C`, `reQF W₀ > 0` on `C ∩ ker K` ⇒ `W₀ + λ K†K ≥ 0` on `C`), `exists_kernel_penalty_eps`, `trace_penalty`, `isCompact_C8`, `cutProduct_eq_smul`, `exists_kernel_penalty_cutProduct`, `kernel_penalty_witness` | `KernelPenalty.lean`. The quadratic form is `MatrixAnalysis.ExtremeCriterion.reQF W v = Re(v† W v)`. The biseparability instance takes `C` = Euclidean-unit cut-product vectors (`C8`, compact) and extends to all cut-product vectors by homogeneity; `kernel_penalty_witness` is the nonstrict form: `W = W₀ + εI + λK†K` is nonnegative on every cut-product vector and `tr(Wρ) = tr(W₀ρ) + ε tr ρ` when `Kρ = 0`. `prop:ppt3-kernel-quant`: the distance bound `g/(2L+λβ)` and the scalar core of `λ = (L + L²/α)/μ` are `MatrixAnalysis.kernel_lift_distance`, `kernel_quant_core`; `prop:ppt3-kernel-quant` is `KernelQuantCuts.kernel_quant_cutProduct` / `kernel_quant_distance` (via `MatrixAnalysis.kernel_quant_form`); not formalised: `rem:ppt3-hand-radius` (hand-checkable constants, exact minors) |
| `thm:ppt3-universal-moments` (cone equivalences) | `biseparable_iff_mem_cone`, `dual_iff`, `mem_range_of_sum_eq` | for any `B` of full column rank and `T_c` with the `CutCurve` property; no Hermiticity needed, `T_c` invertibility not used |
| `thm:ppt3-universal-moments` (curve part) | `cofCoeff_indep`, `exists_smul_cof3_of_mulVec_eq_zero`, `rowsIndep_pencil`, `curveMat_injective`, `curve_cut`, `ppt3_universal_moments` | unconditional given `Kᴴ B = 0`, `B` injective and "`range K` has no nonzero cut-product vector"; the independence of the five quartic coefficient vectors is proved elementarily (Bezout in the chart `a = (1,t)` plus a degree count), no Kronecker form |
| `thm:ppt3-universal-moments` (at most 25 terms; closedness of the cone) | `ConvexGeometry.ConeCar.exists_coneRep_card_le` (conic Carathéodory: a conic combination of elements of `S ⊆ V`, with a linear functional positive on `S`, needs at most `finrank V` terms), `ConvexGeometry.ConeCar.isClosed_cone_of_isCompact`, `finrank_hermitian_le`, `biseparable_card_le_25`, `isClosed_inMomentCone`; for all of `ℂ⁸`: `isBiseparable_iff_cone`, `isClosed_isBiseparable`, `isBiseparable_card_le_64` | `ConvexGeometry/ConeCaratheodory.lean` (generic, Mathlib has only the convex-hull Carathéodory), `MomentConeCaratheodory.lean`. `biseparable_card_le_25` assumes `CutCurve B T` with every `T c` invertible (as in `ppt3_universal_moments`) and gives `n ≤ 25` cut-product vectors `φᵢ` with `B X Bᴴ = ∑ |φᵢ⟩⟨φᵢ|`. Closedness of `∑_c T_c 𝓜₄ T_cᴴ` is derived as the preimage of the closed set of biseparable operators under `X ↦ B X Bᴴ` (the paper argues directly with compactness of the trace-one product projectors in `R`; same idea). Unconditional extra: the whole biseparable cone of three qubits is closed, with at most 64 terms |
| `thm:ppt3-universal-moments` for fully-PPT GME states | `ppt3_universal_moments_of_gme` | unconditional (via `pptSeparable23`); `B`, `K` full-rank with `Kᴴ B = 0`, `ρ K = 0`. The conclusion's `CutCurve` with invertible `T c` feeds `biseparable_card_le_25` and `isClosed_inMomentCone` |

Not formalised: the exact rank computations for the parametric extremality (all `Q`, and `σ₆`) and the moduli ranks (the criterion itself is formalised, `MatrixAnalysis/ExtremeCriterion.lean`; extremality of the single point `σ` is row `cor:ppt3-extreme5` above); the level-two (DPS) noise certificates; the white-noise
upper bounds (they need Gurvits--Barnum).

## Gurvits–Barnum separable ball (general bipartite; used by the PPT THREE QUBIT paper)

Lean files: `FormalResearch/GurvitsBarnum/*.lean`, aggregate `FormalResearch/GurvitsBarnum.lean` (imports Mathlib only).
Source: L. Gurvits and H. Barnum, PRA 66, 062311 (2002). The development holds for any finite index types `ι`, `κ`.
`IsSeparable X` means `X` is a finite sum of `(a a†) ⊗ (b b†)`, and `IsBlockPositive W` means `⟨a⊗b, W a⊗b⟩ ≥ 0` (real part).
All headlines depend only on `[propext, Classical.choice, Quot.sound]` (pinned guards); there is no `native_decide`.

| statement | declarations | notes |
|---|---|---|
| separable ball: `Δ` Hermitian, `‖Δ‖₂ ≤ 1` ⇒ `1 + Δ` separable | `gurvits_barnum`, `isSeparable_of_sum_norm_sq_sub_smul_one_le` (`‖Y − cI‖₂ ≤ c` ⇒ `Y` separable) | Frobenius norm as `∑ ‖Δ p q‖²` |
| block-positive witness inequality `‖W‖₂ ≤ tr W` | `sum_norm_sq_le_trace_sq_of_blockPositive`, `Witness.trace_mul_one_add_nonneg` | equivalent to the ball by duality |
| positive unital maps are contractive (finite-dimensional Russo–Dye) | `IsPositiveMap.contraction`, `IsPositiveMap.norm_dot_le`, `Contr.bdd_map_unitary`, `contractionBound_of_isPositiveMap` | Cayley-transform spectral theorem for unitaries; an invertible contraction is the average of two unitaries |
| block Cauchy–Schwarz for `id ⊗ φ` | `BlockBound.idTensor_one_add_posSemidef` | |
| Choi map of a witness | `choiMap`, `choiMap_posSemidef`, `star_omega_idTensor_choiMap` | `⟨ω, (id⊗φ_W)(Y) ω⟩ = tr(WY)` |
| separable cone closed, separation | `isCompact_convexHull_of_isCompact`, `isClosed_isSeparable`, `exists_blockPositive_separating` | Carathéodory; `ProperCone.hyperplane_separation_point` |

Not formalised: the multipartite version; the application to the PPT THREE QUBIT upper-bound certificates (those decompositions are checked
by exact Python verifiers).

## Gaudin, Racah and bridge modules

The maintained aggregate also imports the current Gaudin metric/rank chain, Racah Weyl-cell modules and B2/Blaschke bridge modules. They are compiled as part of the current aggregate. This high-level map does not attempt to restate every theorem in those families; use the Lean source and theorem-local project updates for exact scope.

## Wigner 3j/6j recurrences (`FormalResearch/Wigner`)

General, reusable Racah-sum infrastructure (no dependency on Weyl-specific objects), intended for later upstreaming to Physlib.
Spins are rational (`j = 2j/2` allowed), admissibility is `IsNat`/`IsTri`; `√` prefactors are real square roots.
All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`).

| statement | Lean | note |
|---|---|---|
| Racah 3j and 6j sums, `threeJ`, `sixJ` | `Defs`, `ThreeJ` (`racahSum3`, `racahSum6`, `sixJ`, `threeJ`) | DLMF 34.2.4–5, 34.4.2; zero-extended inverse factorial `ifa` |
| 3j sum `j₁`-recurrence for all rational arguments | `Rec3j.racahSum3_recurrence` | telescoping certificate, key identity `Rec3jKey.rec3_key` |
| 3j sum `m`-recurrence | `Rec3m.racahSum3_m_recurrence` | constant telescoping certificate |
| 6j sum first-argument recurrence | `Rec6jSum.racahSum6_recurrence` | key identity `Rec6jKey.rec6_key` (slow build, ~5 min) |
| **DLMF 34.3.14, 34.3.15** (3j recurrences with √ prefactors) | `ThreeJ.threeJ_recurrence_m`, `threeJ_recurrence` | |
| **DLMF 34.5.1** `{j₁ j₂ j₃; 0 j₃ j₂} = (-1)^{j₁+j₂+j₃}/√((2j₂+1)(2j₃+1))` | `SpecialValues.sixJ_zero_left` | single-term Racah sum; checks the normalisation and sign of `sixJ` |
| **DLMF 34.5.7** `{a b c; 1 c b}` (`2b, 2c ≥ 1`) | `SpecialValues.sixJ_one_left` | two-term Racah sum, `t ∈ {N, N+1}` |
| tetrahedral symmetries: column swaps `(12)`, `(23)`, upper/lower exchange in columns 1, 2 | `Symmetry.sixJ_swap12`, `sixJ_swap23`, `sixJ_exch12` | termwise permutation of the seven inverse factorials |
| stretched `3j` (`j₃ = j₁+j₂`), DLMF 34.3.6 | `Stretched3j.threeJ_stretched` | one-term sum; the extremal seed of the minimal-rank `3j` recurrence |
| Regge symmetries, DLMF 34.5.9 and 34.5.10 (all rational arguments, no admissibility hypothesis); the form used by Weyl/P2 `eq:6jRegge` | `Regge.sixJ_regge1`, `sixJ_regge2`, `sixJ_regge1_shifted` | the Racah sum depends only on the triad/quad sums, symmetrically; each Regge move permutes them, so it is a termwise permutation of the seven inverse factorials with the product of the four `Δ²` unchanged (no Whipple 4F3 needed) |
| **DLMF 34.3.17** (3j orthogonality, off-diagonal and norm): for fixed `j₂ j₃ M`, `∑ₘ₂ (L j₂ j₃; M m₂ m₃)(L' j₂ j₃; M m₂ m₃) = δ_{LL'}/(2L+1)`, `m₂+m₃=-M` (finsum over the lattice `m₂ = j₂-k`) | `ThreeJOrth.threeJ_orthogonality` (`tt_norm`, `tt_orth_offdiag`, `tt_norm_ratio`) | same architecture as 34.5.14: Green identity for the `m`-recurrence, ratio chain in `L` from the stretched top rank `L=j₂+j₃` (Chu–Vandermonde, `threeJ_stretched`), `L=0` from `threeJ_zero_right` |
| **DLMF 34.3.16** (3j completeness) on the explicit admissible lattices (`2j₂, 2j₃, j₂+j₃±M` natural) | `ThreeJOrthComplete.threeJ_completeness` | number of admissible ranks = number of admissible projections, so the matrix `√(2L+1)·3j` is square with orthonormal rows, hence columns |
| **DLMF 34.5.14** (orthogonality, both off-diagonal and norm): `∑ (2j₃+1)(2l₃+1){j₁ j₂ j₃; l₁ l₂ l₃}{j₁ j₂ j₃; l₁ l₂ l₃'} = δ_{l₃ l₃'}`, sum over the lattice `j₃ = j₁+j₂-k` (finsum; the zero extension restricts it to the admissible range), hypotheses `IsTri j₁ l₂ l₃`, `IsTri l₁ j₂ l₃` and the same for `l₃'` | `Orthog.OrthogMain.sixJ_orthogonality` (`orth_norm`; off-diagonal `OrthogOff.sixJ_orth_offdiag`; `OrthogRec.sixJ_recurrence_ext`) | Off-diagonal: discrete Green identity for the three-term recurrence in the weight `2j₃+1` (`OrthogAbs.green_lsum`). Norm: ratio chain along the `μ` lattice (`OrthogRatio`) from the minimal case, where the sum is a Dougall terminating very-well-poised `₅F₄` sum (`OrthogDougall.dougall_sum`, creative-telescoping certificate) via `OrthogBase`; the `μ=0→1` step is separate (`orth_norm_step_zero`). New symmetries `sixJ_exch23`, `sixJ_swap13` |
| `3j` symmetries, DLMF 34.3.8–10 (all rational arguments; `sgn J` = `(-1)^J` for integer `J`, `0` otherwise): column swaps (even permutations invariant, odd ones give `(-1)^J`), `m ↦ -m` | `ThreeJSym.threeJ_swap12`, `threeJ_swap23`, `threeJ_swap13`, `threeJ_cyc`, `threeJ_cyc'`, `threeJ_neg`, `threeJ_eq_zero_of_not_int` | termwise: reflect the Racah index (`s ↦ j₁+j₂-j₃-s`, or `s ↦ j₁-m₁-s`) and track the sign with `sgn` |
| DLMF 34.3.1 (`(j₁ j₂ 0; m₁ m₂ 0)`) | `Special3j.threeJ_zero_right` (and `threeJ_zero_right_of_ne`, a triangle-condition consequence) | one-term sum |
| DLMF 34.3.5 (`(j₁ j₂ j₃; 0 0 0)`): odd `J` vanishes, even `J` closed form | `Special3j.threeJ_zero_of_odd`; `Special3jEven.threeJ_zero_zero_zero_even`, `threeJ_zero_zero_zero`, `racahSum3_dixon` | odd: from `threeJ_neg`. Even: for `m₁=m₂=0` the `racahSum3` recurrence degenerates to a two-term one, run from the one-term stretched value |
| DLMF 34.5.2 (`{j₁ j₂ j₃; ½ j₃-½ j₂+½}`) | `Special6j.sixJ_half_a` | one-term sum |
| **DLMF 34.5.11–13** (6j recurrence with √ prefactors) | `SixJRecurrence.sixJ_recurrence` | `IsTri` hypotheses; vanishes when fixed triads fail |

Not formalised: DLMF 34.5.3, and the bridge theorem is proved on the Physlib fork branch `cmbant/physlib` `bridge-sixj` (not upstream): `sixJ_eq_racah6j`, Racah's closed formula for Physlib's operator-defined `sixJ` for `0 < a`, `0 < c` and `ValidA`/`ValidB` (via `sixJ = Cconst · Xs`, a balanced terminating `₄F₃`, and one Sears transformation), axioms `[propext, Classical.choice, Quot.sound]`, compiled on Lean 4.35 / Mathlib `56a0058`. Not covered there: `a = 0` or `c = 0`, vanishing for inadmissible labels, and the operator-side three-term recurrence (`casMat_eq` is `sorry`). Certificate search scripts: `scripts/wigner_certificates/` (provenance only).

### Jacobi polynomials (`FormalResearch/Special/Jacobi*.lean`, namespace `FormalResearch.Special`)

DLMF chapter 18, for the real polynomial `jacobi α β n` (`P_n^{(α,β)}`, arbitrary real `α β` unless stated). All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`).

| statement | Lean | file | note |
|---|---|---|---|
| definition, DLMF 18.5.7 (explicit sum in `((x-1)/2)^ℓ`, valid at the exceptional parameters) | `jacobi` | `JacobiDef` | |
| values at `±1` and reflection, DLMF 18.6.1; derivative 18.9.15; ODE 18.8.1 (and its self-adjoint form) | `jacobi_eval_one`, `jacobi_eval_neg_one`, `jacobi_comp_neg`, `derivative_jacobi`, `jacobi_ode`, `jacobi_sturmLiouville`, `jacobiSL_all` | `JacobiBasic` | all real `α β` (the Sturm–Liouville form for natural `α β`); proved in the basis `(X-1)^ℓ` by the coefficient ratio recurrence |
| three-term recurrence DLMF 18.9.1 (denominator-free, and normalised for `α+β+2 > 0`) | `jacobi_three_term`, `jacobi_one`, `jacobi_X_mul_succ`, `jacobi_X_mul_zero` | `JacobiRec` | all real `α β`, including `α+β+n ∈ ℤ_{≤0}` |
| degree and leading coefficient (DLMF 18.3); abstract Sturm–Liouville orthogonality; orthogonality to lower degrees; `∫_0^π f(cos θ) sin θ dθ = ∫_{-1}^1 f` | `natDegree_jacobi_le`, `jacobi_coeff_self`, `sturm_liouville_orth`, `jacobi_orth_lowerDegree`, `beta_nat`, `integral_cos_substitution` | `JacobiInt` | natural parameters (polynomial weight) |
| orthogonality and norm for natural `α=a`, `β=b` (DLMF 18.3, table 18.3.1); the `cos θ` form used for Wigner `d` | `jacobi_orthogonal`, `jacobi_orthogonal_lowerDegree`, `jacobi_norm`, `jacobi_norm_cos` | `JacobiOrth` | norm from `⟨x P_n, P_{n+1}⟩` computed twice, base case the Beta integral |
| the Jacobi weight and Beta integral for real `α, β > -1` (via `Γ`) | `jacobiW_intervalIntegrable`, `real_betaIntegral`, `jacobi_beta_integral` | `JacobiBeta` | |
| orthogonality and norm for real `α, β > -1` (`2^{α+β+1}/(2n+α+β+1) · Γ(n+α+1)Γ(n+β+1)/(Γ(n+α+β+1) n!)`) | `jacobi_orthogonal_real`, `jacobi_orthogonal_lowerDegree_real`, `jacobi_norm_real_zero`, `jacobi_norm_real` | `JacobiOrthReal` | `jacobi_norm_real` excludes `n = 0`, `α+β+1 = 0` (closed form `0/0`); that case is `jacobi_norm_real_zero` |
| zeros: `n` simple real zeros, all in `(-1,1)`, `P_n` splits and is separable | `roots_of_orth`, `jacobi_roots_nodup`, `jacobi_roots_card`, `jacobi_roots_mem`, `jacobi_splits`, `jacobi_separable`, `jacobi_natDegree` | `JacobiZeros` | natural `a b` only (sign-change argument through the factorisation of `P`); real `α, β` not formalised |
| Christoffel–Darboux DLMF 18.2.12, confluent form 18.2.13 | `jacobi_christoffel_darboux`, `jacobi_christoffel_darboux_coeff`, `jacobi_christoffel_darboux_confluent`, `jacAlpha_mul_jacNorm`, `jacAlpha_eq_coeff_div` | `JacobiCD` | natural `a b` |
| link to the `₂F₁` of `bernstein_hahn_jacobi`: `∑_k (-n)_k (n+α+β+1)_k/((α+1)_k k!) t^k = n!/(α+1)_n · P_n^{(α,β)}(1-2t)` | `hypergeometric_eq_jacobi` | `JacobiCD` | identifies the Jacobi side of `P2HahnBeta` with `jacobi` |
| Rodrigues' formula DLMF 18.5.5; two-sided sum 18.5.8 (as a polynomial identity) | `jacobi_rodrigues`, `jacobi_twoSided_poly` | `JacobiSpecial` | natural `a b` |
| Mathlib links: Legendre (`shiftedLegendre`, DLMF 18.7.9, with Mathlib's `P̃_n(x) = P_n(1-2x)` convention), Chebyshev `T` (18.7.3) and `U` (18.7.4), Gegenbauer (18.7.1) | `jacobi_zero_zero_eq_shiftedLegendre`, `jacobi_chebyshevT`, `chebyshevT_eq_jacobi`, `jacobi_chebyshevU`, `chebyshevU_eq_jacobi`, `gegenbauer`, `gegenbauer_comp_neg`, `gegenbauer_three_term` | `JacobiSpecial` | |

### Wigner small `d`-function (`FormalResearch/Wigner/WignerD*.lean`)

`wignerSmallD j m' m θ = d^j_{m'm}(θ) = ⟨j m'| exp(-iθJ_y) |j m⟩` (Condon–Shortley; checked against `sympy.physics.quantum.spin.Rotation.d` for `j ≤ 3`), spins rational,
zero-extended factorials as in `threeJ`. All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`).
Real-variable form `wignerSmallDx j m' m x = d(arccos x)`.

| statement | Lean | file | note |
|---|---|---|---|
| definition (Edmonds 4.1.15), textbook-exponent form, vanishing unless `m'-m ∈ ℤ`; sanity values (`j = 1/2` table, `d^1_{00}`, `d^1_{10}`, `d^1_{11}`, `θ = 0`) | `wignerSmallD`, `wignerSmallD_eq_textbook`, `wignerSmallD_eq_zero_of_not_int`, `wignerSmallD_zero`, `wignerSmallD_half_pp/pm/mp/mm`, `wignerSmallD_one_zero_zero`, `wignerSmallD_one_one_zero`, `wignerSmallD_one_one_one` | `WignerD` | |
| symmetries (Varshalovich 4.4.1): `d^j_{m'm} = (-1)^{m'-m} d^j_{mm'} = d^j_{-m,-m'}`, `d(-θ) = d^T` | `wignerSmallD_swap`, `wignerSmallD_neg`, `wignerSmallD_neg_theta` | `WignerD` | termwise reindexing |
| Jacobi form in all four chambers: `d^j_{m'm} = (-1)^μ √(k!(k+μ+ν)!/((k+μ)!(k+ν)!)) sin(θ/2)^μ cos(θ/2)^ν P_k^{(μ,ν)}(cos θ)` (`μ = m'-m`, `ν = m'+m`, `k = j-m'` in chamber A; the other three by the symmetries) | `wignerSmallD_eq_jacobi`, `wignerSmallD_chamber_A`, `_B`, `_C`, `_D`, `jacobi_eval_nat_twoSided` | `WignerDJacobi` | uses the two-sided sum 18.5.8 for natural `μ, ν` (Vandermonde) |
| orthogonality and norm in the rank: `∫_0^π d^j_{m'm} d^{j'}_{m'm} sin θ dθ = 2/(2j+1) δ_{jj'}` (Varshalovich 4.10.1(1)) | `wignerSmallD_orthogonal`, `wignerSmallD_norm`, `wignerJacobiForm_orth` | `WignerDOrth` | from `jacobi_orthogonal`, `jacobi_norm_cos`; hypotheses `j ± m`, `j ± m'` natural |
| Wigner differential equation, `eq:dODE`: `D² d + (j(j+1) sin²θ - (m²+m'²-2mm' cos θ)) d = 0`, `D = sin θ ∂_θ` (all rational `j m' m`, all `θ`); `cot` form on `(0,π)`; `x`-form on `(-1,1)` | `wignerSmallD_ode`, `wignerSmallD_ode_cot`, `wignerSmallDx_ode` | `WignerDODE` | via `jacobi_ode` and `wigG_deriv` |
| rank ladders `eq:dranklower`, `eq:drankupper` and the rank recurrence (`eq:3jrank` at `t = 0`, Varshalovich 4.8.1) | `wignerSmallD_rank_lower`, `wignerSmallD_rank_upper`, `wignerSmallD_rank_rec`, `wignerSmallDx_rank_lower`, `wignerSmallDx_rank_upper` | `WignerDLadder` | all rational `f m' m`, no admissibility hypothesis (`R_f = 0` exactly where the neighbouring rank is undefined) |
| Jacobi contiguous relations (Szegő §4.5, DLMF §18.9(iii)) | `jacobi_ladder_lower`, `jacobi_ladder_upper` | `WignerDLadder` | `α+β+1 > 0`; from the coefficient recurrence and `jacobi_three_term` |

### Weyl P2: exact finite 6j/Racah statements (`FormalResearch/Racah/P2Racah*.lean`, namespace `Racah.SixJ`)

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`. This section is the exact finite algebraic part; the analytic half (Λ-expansions, `thm:6jeven`, Wigner `d`,
the `L²(-1,1)` realisations) is in *Weyl P2: analytic half* below.

| paper statement | Lean | file | note |
|---|---|---|---|
| `eq:6jfamily`, `eq:6jPhi` (definitions of the family and the normalised kernel `Φ_f(c)`) | `W6`, `Phi6`, `qf`, `rootR`, `etaK`, `W6_eq_regge_form`, `W6_eq_rank_form` | `P2RacahMidpoint` | `Phi6` uses the zero-extended `sgn`, equal to `(-1)^ξ` on every admissible point |
| `eq:6jRegge`, `eq:symmetricpairs` | `W6_regge_midpoint`, `weyl_shift_pairs` | `P2RacahMidpoint` | `sixJ_regge1_shifted` plus the column-permutation bridge |
| `eq:Ek`, `eq:diagidentity` | `E6_midpoint`, `diag_identity` | `P2RacahMidpoint` | |
| **`lem:6jrec`** (exact midpoint Racah recurrence, `eq:6jrec`) | `Phi6_midpoint_recurrence` | `P2RacahMidpoint` | slightly stronger than the paper: holds on the whole `f` range including boundary rows (`sixJ_recurrence_of_tri` in `P2RacahRec`: 34.5.11 with only the two triads through `j₁`) |
| canonical-sector reductions (swap, upper/lower exchange, phase `(-1)^(m-n)`) | `W6_swap_ab`, `W6_exch_ab`, `Phi6_swap_ab`, `Phi6_exch_ab` | `P2RacahMidpoint` | |
| `eq:cminRacah`–`eq:Racahdimension`; closure `𝒜(c_min)=0=𝒜(c_max+1)` | `cMin`, `cMax`, `fMin`, `fMax`, `cMin_centered`, `cMax_sub_cMin`, `edgeA_cMin`, `edgeA_cMax_succ`, `E6_edgeA` | `P2RacahLattice` | numeric identities only; the "physical lattice = `{c_min..c_max}`" iff statements are not formalised here |
| `eq:RacahDetailedBalance`, `eq:Racahcellwidth`, `eq:RacahD0factor` | `omegaW_aPlus`, `omegaW_succ_aMinus`, `omegaW_eq_cell_width`, `cosA_eq_lawCosinesX`, `D0_factor` | `P2RacahLattice` | |
| `H_R Φ_f = f(f+1)Φ_f` on every row (without orthogonality) | `Phi6_lattice_eigen` | `P2RacahLattice` | |
| `eq:Racahdiagzero` (the `c=0` row), `Φ_f(0)`, `Φ_f(1)` | `Phi6_lattice_row_zero`, `Phi6_zero_value`, `Phi6_one_value` | `P2RacahLatticeEnd` | via 34.5.1, 34.5.7 |
| **`lem:6jseed`** (positive stretched seed, integer and half-integer `m`), `eq:6jseed`, `eq:6jexceptionalseed` | `Phi6_seed`, `Phi6_seed_sq`, `Phi6_exceptional_zero`, `Phi6_exceptional_one` | `P2RacahSeed` | real analyticity of the carrier in `Λ⁻²`: `analyticAt_ptilde6` (`P2AnalyticBulk6j`); rationality in `δ` of the coefficients not formalised |
| `prop:unique` (exact algebraic core) | `unique_affine_core`, `driftX1_eq_zero_iff`, `prop_unique_algebra` | `P2RacahUnique` | expansion half of the proposition not formalised (the expansion theorem it would use is `thm_6jeven`, below) |
| physical `c`- and `f`-lattices are `{c_min..c_max}`, `{f_min..f_max}` (iff statements under `RacahLabels`: `2a, 2b, 2m, m-n ∈ ℤ`), equal cardinality `eq:Racahdimension` | `physC`, `physF`, `mem_physC_iff`, `mem_physF_iff`, `ncard_physC_eq_ncard_physF` | `P2RacahSystemLattice` | |
| `eq:RacahHamiltonian` as a concrete matrix; self-adjointness in the weight `ω_c` | `HR`, `wgtR`, `HR_selfadjoint_entries`, `HR_selfadjoint`, `HRsym_isHermitian` | `P2RacahSystemOp` | |
| `eq:RacahPhiOrthogonality` (from 34.5.14) | `sixJ_orth_physical`, `weight_Phi_mul`, `Phi6_orthogonality` | `P2RacahSystemOrth` | |
| orthonormal eigenbasis `v_f`, `eq:RacahPhiCompleteness`, spectrum `{f(f+1)}`, simplicity, characteristic polynomial | `vR_eigen`, `vR_orthonormal`, `Phi6_completeness`, `vR_expansion`, `HR_spectrum`, `HR_eigenspace`, `HR_charpoly` | `P2RacahSystemSpec` | completeness by the dimension identity (square matrix with orthonormal rows) |
| **`thm:6jfiniteRacah`** (exact finite self-adjoint Racah–Wigner system) | `thm_6jfiniteRacah` (hypothesis `RacahSystem a b m n D`, satisfiable iff the lattice is non-empty) | `P2RacahSystem` | conjunction of the lattice, detailed-balance, eigen, orthonormality, completeness, spectrum, simplicity and charpoly statements |
| Racah-to-Wigner spectral map (`prop:6jRacahTransmutation`) | `SRmap`, `SRmap_u`, `SRmap_isometry`, `SRmap_SRinv`, `SRinv_SRmap`, `SRmap_intertwine` | `P2RacahSystemWigner` | **abstract form**: orthonormal family in a real inner-product space. The realisation in `L²(-1,1)` with Wigner `d`-functions and the kernel `eq:6jRacahKernel` is `prop_6jRacahTransmutation`, `SR_kernel`, `SR_intertwine_diff` (`P2AnalyticL2Transmutation`) |
| **Racah-polynomial realization** (`eq:physicalRacah4F3`, `eq:physicalRacahParameters`): `Φ_{m+r}(c_min+y)/Φ_m(c_min+y)` is the terminating `₄F₃(-r, r+2m+1, -y, y+2c_min+1; m-n+1, m+n+c_min+c_max+2, -D; 1)` | `ppR_eq_racahPoly`, `physQ`, `racahPoly`, `racahPoly_diff` | `P2RacahPolyIdent`, `P2RacahPolyDiff` | proved by uniqueness of the solution of the three-term difference equation (6j side: `ppR_row`; polynomial side: `racahPoly_diff`), not by a rearrangement of sums |
| `eq:physicalRacahExplicit`, `eq:physicalRacahweight`, **`eq:physicalRacahPolyOrth`** (Racah weight `π_c = ω_c(2m+1)Φ_m²/2` positive; orthonormality; `∑π_c = 1`) | `physR_eq`, `physPi_eq`, `physPi_pos`, `physR_orthonormal`, `physPi_sum` | `P2RacahPolyOrth` | orthonormality from `Phi6_orthogonality_fin` (34.5.14) |
| `eq:RacahGroundTransform`, `eq:RacahPolyEigenvalue` (ground-state transform is the standard Racah difference operator, eigenvalue `r(r+2m+1)`) | `groundTransform_eq`, `groundTransform_physR` | `P2RacahPolyGround` | |

### Weyl P2: exact finite 3j statements (`FormalResearch/Racah/P2ThreeJ*.lean`)

Notation as in the paper's `eq:3jPhi`: `Phi3j L M σ N μ = sgn(2L+j₊+m₊)·√N·threeJ L j₋ j₊ M m₋ m₊` with `j∓ = (N-1∓σ)/2`, `m₋ = μ-M/2`,
`m₊ = -μ-M/2`; zero off the integer domain. This section is the exact finite algebra, including the finite spectral statements of `thm:3jspectral`
(orthogonality and completeness in the last rows); the analytic half (`thm:3jeven`, Wigner `d`, `L²(-1,1)`) is in *Weyl P2: analytic half* below.

| paper statement | Lean | file | note |
|---|---|---|---|
| 34.3.14, 34.3.15 without hypotheses on the neighbouring symbols (closes the boundary rows) | `threeJ_recurrence_all`, `threeJ_recurrence_m_all`, `racahSum3_zero_of_not_isNat` | `P2ThreeJRecAll`, `P2ThreeJVanish` | |
| `eq:3jrank`, `eq:rankJacobiForm` (exact rank recurrence of the normalised kernel) | `Phi3j_rank_recurrence`, `Phi3j_rank_jacobi` | `P2ThreeJRec` | verbatim, including boundary ranks |
| `eq:3jdiff` (exact finite-difference equation in `x`) | `PhiX_midpoint_diff`, `aMid_neg_N`, `aMid_zero_top`, `aMid_zero_bottom` | `P2ThreeJRec` | |
| operator even in `h`; `𝖧_h Φ_L = L(L+1)Φ_L`; symmetric on the lattice | `Dop_neg_h`, `Hh_Phi`, `Hh_lattice_symmetric` | `P2ThreeJOperator` | |
| `eq:3jseed`, `eq:3jPiL`, evenness of `𝔠_r` | `Phi3j_seed`, `Cprod_neg`, `Cprod_one_odd`, `Cprod_one_even` | `P2ThreeJSeed` | from Racah's one-term sum |
| `rem:spinhalf` (all four chambers), `M ↦ -M` | `Phi3j_half_pp/pm/mp/mm`, `Phi3j_neg_M` | `P2ThreeJSym` | `d^{1/2}` written as `√((1±x)/2)` |
| **`eq:3jRegge`** (Regge symmetry of the 3j kernel, finite `N`), `eq:coeffRegge`; edge-chamber seeds | `threeJ_regge_mid`, `Phi3j_regge`, `Phi3j_edge_sigma_neg`, `Phi3j_edge_M_neg`, `Phi3j_edge_sigma_pos` | `P2ThreeJRegge` | by descent in `L` from the stretched seed using the rank recurrence (no Racah-sum transformation) |
| `prop:3junique` (exact algebraic core) | `affine_center_eq`, `wigner_principal_affine`, `principal_coeffs`, `affine_midpoint_unique` | `P2ThreeJUnique` | the continuum-expansion step is a hypothesis; the expansion half is not formalised |
| Hahn dictionary, `eq:ExactHahnKernel` for `n = 0` | `hahnW_sum`, `hahn_x_of_u`, `Phi3j_hahn_zero` | `P2ThreeJHahn` | the general `n` is in the next rows |
| **`eq:ExactHahnKernel`, all `0 ≤ n ≤ D`**: `Φ_{M+n}` is `(-1)^α √(N/(2L+1)) √(w_H/h_n) Q_n(u)` | `Phi3j_hahn`, `hahnQ_rec` (Hahn three-term recurrence as a finite identity), `kernel_ind`, `kernel_norm`, `Phi3j_L1_M0` | `P2HahnKernel`, `P2HahnRec`, `P2HahnL1` | by induction in `n` from `Phi3j_hahn_zero` using the rank recurrence (no `₃F₂` transformation); the Hahn norm is identified from `Phi_discorth` |
| **`eq:HahnAllChamberPhase`** (all four chambers, phase `ε`), `eq:HahnInvariantParameters`, `eq:DualHahnSpectralCoordinate` | `Phi3j_hahn_all_chambers`, `hahnQ_reflect`, `hahnNorm_reflect`, `hahn_normalized_reflect`, `hahn_alpha_add_beta`, `dualHahn_spectral` | `P2HahnChambers`, `P2HahnReflect` | chambers via `Phi3j_regge`, `Phi3j_neg_M` and the finite Hahn reflection `Q_n(D-u; β, α, D) = (-1)^n ((α+1)_n/(β+1)_n) Q_n(u; α, β, D)` |
| `prop:HahnJacobi` (exact finite Hahn algebra: `[C,X] = 2(X²-1)+4h²(H-(Σ-1)/2)`, `[H,C] = 2{H,X}-4Mσ`) | `Cop`, `finiteHahn1`, `finiteHahn2`, `finiteHahn2_lattice` | `P2HahnAlgebra` | the second relation needs the edge conditions on `x` (or the four `IsNat` conditions) |
| `lem:polarintertwiner` (polar unitary of a finite intertwiner, finite-dimensional complex Hilbert spaces) | `gram_commute`, `polarU_unitary`, `polarU_intertwines` | `P2HahnPolar` | over `ℂ` (Mathlib functional calculus); the real case follows by complexification |
| beta–binomial realization, finite part: Bernstein–Hahn–Jacobi identity `eq:BernsteinHahnJacobi` (Jacobi side as the terminating `₂F₁`), singular values `eq:singularvaluesgeneral`, `eq:physicalsingularvalues` | `bernstein_moment`, `bernstein_hahn_jacobi`, `singularSq`, `singularSq_pos`, `singularSq_physical` | `P2HahnBeta` | `prop:SN` is `prop_SN` (`P2AnalyticL2Transmutation`) and the singular-pair relation is `singular_pair` (`P2AnalyticL2Singular`); the Jacobi side is identified with `jacobi` by `hypergeometric_eq_jacobi` |
| `eq:3jdiscorth`, `eq:3jdisccomplete` (hypothesis `SpecAdm M σ N` encodes the paper's integrality assumptions) | `Phi_discorth`, `Phi_disccomplete` | `P2ThreeJSystem` | from 34.3.17 / 34.3.16 |
| spectrum of `𝖧_h` is `{L(L+1)}`, simple; eigenvectors multiples of `Φ_L` (`thm:3jspectral`, the finite part) | `Hh_spectrum_iff`, `Phi_latEigen`, `rankEig_strictMono`, `Hh_eigen_simple` | `P2ThreeJSystemSpec` | symmetry from `Hh_lattice_symmetric` |



### Weyl P2: analytic half (`FormalResearch/Racah/P2Analytic*.lean`)

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`. Merged to `master` from branch `wigner-3j6j` (PR #81). All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`).
Conventions: `Phi3j L M σ N μ` at `x = 2μ/N`, `t = h² = N⁻²`; `Phi6 … f m n` at `A = wA a n`, `B = wB b m`, `C = wC c`, `S = A+B+C`; the paper's `d^L_{Mσ}(arccos x)` is
`wignerSmallDx L M σ x`; `Lat4`/`SpecAdm` (3j) and the four integrality facts `f ± m`, `f ± n ∈ ℕ` (6j) encode the physical lattice.

| paper statement | Lean | file | note |
|---|---|---|---|
| `lem:centeredshift` (central products `𝔠_r(u,h)` as `Ct r u t`, `t = h²`; analyticity, positivity, log estimate, `Γ`-ratio form); uniform Taylor remainder of a jointly smooth `G(z,t)` in `t` | `Ct`, `Cprod_eq_Ct`, `Ct_zero_t`, `analyticAt_Ct`, `Ct_pos`, `abs_log_Ct_sub_le`, `Ct_Gamma`; `taylor_mean_remainder_bound`, `taylorCoeff` | `P2AnalyticCt`, `P2AnalyticCore`, `P2AnalyticTaylor` | generic analytic input of every expansion below; scalar analytic propagation `analyticAt_recurrence_two`, central-binomial convolution `sum_centralBinom_mul` |
| **`lem:sqrtfreecarrier`**, 3j (`eq:sqrtfreecarrier`, `eq:3jrankpoly`; all four chambers, all ranks `L ≤ N-1`) | `ptilde3`, `ptilde3Poly`, `Phi3j_carrier`, `Phi3j_eq_Gc3`, `ptilde3_rank_poly`, `natDegree_ptilde3Poly_le`, `dZero3_rank_rec` | `P2AnalyticCarrier3j{,Def,Seed,Rec}` | closed-form germ `Gc3 M σ k x t`; polynomial in `τ` of degree `≤ k`, constant leading coefficient `lead3` |
| **`lem:sqrtfreecarrier`**, 6j (`eq:6jrankpoly`, `eq:6jEdgeProducts`, `lem:6jseed`, `eq:6jexceptionalseed`; all chambers) | `ptilde6`, `ptPoly`, `piSix`, `Phi6_seed_carrier`, `Phi6_carrier_canonical`, `edgeSq_eq_EW_sq` | `P2AnalyticCarrier6j{,Induction,Chambers,Shape,Poly}` | germ `G6 f m n α β γ t` |
| `t = 0` carrier is Wigner `d` (`G(x,0) = d^L_{Mσ}(arccos x)`, 3j; `G_{f,0} = d^f_{nm}(arccos x)`, 6j including the transposition phase `(-1)^{m-n}` of chambers II/III) | `dZero3_eq_wignerD`, `Gc3_zero_eq_wignerD`; `dZero6c_eq_wignerD`, `dZero6_eq_wignerD`, `G6_zero_eq_wignerD` | `P2AnalyticBridge3j`, `P2AnalyticBridge6j` | induction in the rank against `wignerSmallDx_rank_rec` |
| `eq:WignerJacobiMonic` (`d = k W P̂^{(p₊,p₋)}`, `k_{3j} = lead3`, `k_{6j} = kLead`) | `lead3_eq_jacobi`, `lead3_eq_closed`, `wignerD3_eq_lead_mul_monic`; `kLead_eq_jacobi`, `kLead_eq_closed`, `wignerD6_eq_kLead_mul_monic` | `P2AnalyticLeading` | constants identified by comparing top coefficients; 3j all chambers; 6j Wigner form in the canonical chamber (`m ∓ n` natural); 6j carrier-polynomial leading coefficient `ε(n,m)·κ_d(|m-n|,|m+n|) ≠ 0` in all four chambers: `kLeadAll_eq_signE3_mul_kappa`, `kLeadAll_ne_zero`, `carrierPolyAll_natDegree`, `Phi6_eq_poly_all` (`P2AnalyticLeading6jChambers`); all-chamber Wigner form `d = k_{6j} W P̂` not formalised |
| **`thm:3jeven`** (`eq:3jevenexp`): analytic germ `G` on `U × (-ρ,ρ)`, `Φ = G(x,N⁻²)`, `f_0 = d`, expansion in `N⁻²` to every order with remainder `O_K(N^{-2R})`, `f_{2r}` analytic on `(-1,1)` | `thm_3jeven`, `thm_3jeven_noOdd`, `thm_3jeven_leading`, `Phi3j_even_expansion`, `Gc3_analytic_box`, `analyticOnNhd_f3even`, `analyticOnNhd_wignerSmallDx_of_labels` | `P2AnalyticHeadline`, `P2AnalyticBulk3j` | |
| `cor:3jcoeffsym` (`eq:coeffRegge`, `eq:coeffSign`, `eq:coeffTranspose`), `rem:spinhalf`, `rem:movingpoint` | `f3even_regge`, `f3even_negMσ`, `f3even_swap`; `Phi3j_half_exact`, `Phi3j_half_expansion`; `Phi3j_moving_point`, `rem_movingpoint` | `P2AnalyticBulk3j`, `P2AnalyticHeadline` | coefficientwise from the exact symmetries of `Gc3` |
| **`thm:6jeven`** (`eq:6jleading`, `eq:6jevenexp`): `G_{f,2r}` analytic and homogeneous of degree `-2r` on the strict-triangle cone, `G_{f,0} = d^f_{nm}(arccos x)`, germ in `S⁻²` with uniform radius over compact shape sets, `Φ_f = ∑_{r<R} G_{f,2r} + O(H^{-2R})` on `T_δ` | `thm_6jeven`, `Phi6_even_expansion`, `Phi6_even_expansion_cone`, `G6even`, `G6even_homogeneous`, `analyticOnNhd_G6even`, `Phi6_eq_G6` | `P2AnalyticHeadline6j`, `P2AnalyticBulk6j` | holomorphy paragraph of `lem:6jseed` in its real-analytic form (`analyticAt_ptilde6`); `StrictTri`, `TriDelta` |
| **`thm:uniformedge`** (a) (`eq:3juniformedge`) and (b) (`eq:6juniformedge`), `W s_0 = d`; edge-factor bounds `0 < c ≤ E ≤ 1` and `eq:edgefactoroverlap`, `eq:universalEdgeFactor` | `thm_uniformedge_3j`, `Phi3j_uniform_edge`, `edgeS3`, `natDegree_edgeS3_le`; `thm_uniformedge_6j`, `Phi6_uniform_edge`, `Phi6_edge_factor`, `edgeE_bounds`, `edgeR_pos_le_one`, `edgeR_expansion`, `analyticOnNhd_cKc` | `P2AnalyticHeadline`, `P2AnalyticHeadline6j`, `P2AnalyticUniform3j`, `P2AnalyticUniform6j` | uniform on the whole physical lattice; the 6j coefficients `s_r` are analytic in `δ ∈ (-1,1)` (rationality in `δ` with poles at `±1` not formalised); `0 < c ≤ E ≤ 1` is for the 6j edge factor (the 3j edge-factor bounds alone are not stated) |
| **`thm:3jNLO`** (`eq:3jimproved`, `eq:3jf2`, `eq:3jf2seednorm`), Gaunt remark to `N⁻²` | `f3even_one_eq_nloF2`, `Phi3j_nlo_expansion`, `Phi3j_gaunt_nlo`, `nloH_rec`, `nlo_seed_alg`, `nlo_e_eq`, `qt3_rank`, `f3even_one_eq` | `P2AnalyticNLO3j{,Alg,Deriv}` | remainder `C N⁻⁴`; inhomogeneous rank recurrence for `f_2 - (2L+1)L(L+1)d_L/12` from the ladders differentiated once and the ODE. The Gaunt `N⁻⁴` coefficient `J(5J-4)/32` needs `thm:3jNNLO` and is not formalised |
| **`cor:uniformNLO`**, 3j half (`eq:3juniformNLO`) | `Phi3j_uniform_nlo` | `P2AnalyticNLO3jUniform` | explicit polynomial form of `N⁻²f_2 - e_2 d` not formalised |
| **`cor:uniformNLO`**, 6j half (`eq:6juniformNLO`) | `Phi6_uniform_nlo`, `edgeW_mul_s6_one`, `G6closed_sub_e2_eq_poly` | `P2AnalyticNLO6jUniform` | proved under the ratio bound `λ ≤ A/B ≤ λ⁻¹` of `eq:6jedgeratiobound`, which the paper's corollary statement omits (needed for the `O((A+B)⁻⁴)` remainder); `W ×` polynomial form of `G_{f,2} - e_2^{6j} d` proved |
| **`thm:6jclosedcorrection`** (`eq:6jclosedg`, `eq:6jPf`, `eq:6jQf`, `eq:grec`, `eq:kappaClosedMatch`), all four chambers | `a6_one_closed`, `G6even_one_eq_closed`, `Phi6_nlo_expansion`, `Phi6_nlo_expansion_cone`, `nlo6_e_eq`, `nlo6H_rec`, `nlo6_seed_alg`, `nlo6P`, `nlo6Q` | `P2AnalyticNLO6j{,Alg,Deriv}` | remainder `C S⁻⁴` on compact shape sets, `C H⁻⁴` on `T_δ`; no `6j` degree `-4` term |
| `eq:continuummass` (`rem:normmatch`): `∫_{-1}^1 d^L_{Mσ} d^{L'}_{Mσ} dx = 2/(2L+1) δ_{LL'}`; Wigner modes `u_L` orthonormal in `L²(-1,1)`; `𝖧₀ u_L = L(L+1) u_L` (`eq:H0`) | `integral_wignerSmallDx_mul`, `integral_wignerSmallDx_sq`, `uWig`, `integral_uWig_mul`, `L2uWig_orthonormal`, `H0diff`, `H0diff_uWig`, `H0diff_sum` | `P2AnalyticL2Wigner` | `L2cont` is the class in `Lp ℝ 2 (volume.restrict (Icc (-1) 1))` |
| **`prop:SN`** (`eq:SNspectral`–`eq:SNintertwine`): `S_N u_L = v_L`, isometry, unitary from `span{u_L}` onto `ℓ²(𝒳_N,2h)`, `𝖧_h S_N = S_N 𝖧₀`; kernel `eq:SNkernel` | `vN_orthonormal`, `vN_expansion`, `SNmap_u`, `SNmap_isometry`, `SNmap_intertwine` (abstract, `P2AnalyticL2ThreeJ`); `uN_orthonormal`, `prop_SN`, `SN_kernel`, `SN_intertwine_diff` | `P2AnalyticL2ThreeJ`, `P2AnalyticL2Transmutation` | `𝒱_N` is the finite span, as in the paper; `S_N` on all of `L²` and `L²` completeness of `{u_L}` not formalised |
| **`prop:6jRacahTransmutation`** (`eq:6jRacahSpectralMap`–`eq:6jRacahIntertwine`), kernel `eq:6jRacahKernel` | `uR_orthonormal`, `prop_6jRacahTransmutation`, `SR_kernel`, `SR_intertwine_diff` | `P2AnalyticL2Transmutation` | exactly parallel to `prop_SN`, under `RacahSystem a b m n D` |
| **`prop:betabinomialpolar`**, singular-pair relation `T_D J_n = s_n H_n` (`eq:singularvaluesgeneral`, `eq:betameasure`–`eq:conditionalC`, `eq:BernsteinAdjoint`) | `singular_pair`, `norm_relation`, `Cop_jT`, `ipP_Cop`, `ipJ_jT_orth`, `hahn_orth`, `hahn_determined`, `pD_eq_hahnW`, `beta01` | `P2AnalyticL2Singular` | Jacobi orthogonality in `L²(ν_H)`, Hahn orthogonality in `ℓ²(p_D)`; polar decomposition, gauges and `eq:SNpolar` are in the next row |
| **`prop:betabinomialpolar`** polar part: `U_D = T_D(T_D^*T_D)^{-1/2}`, `U_D J_n = H_n`, gauges `G_c`, `G_d`, **`eq:SNpolar`** `S_N G_c = G_d U_D`, whitening `eq:SNwhitening`, `eq:physicalsingularvalues` and its Gamma form | `polarFactor`, `polarFactor_basis`, `polarFactor_intertwine` (abstract, `lem:polarintertwiner`); `UD_JV`, `UD_unitary`; `vN_eq_Gd`, `uN_eq_Gc`, `Gc_inner`, `eq_SNpolar`, `eq_SNpolar_inv`, `eq_SNwhitening`, `sing_sq_physical`, `sing_sq_gamma`, `prop_betabinomialpolar` | `P2AnalyticL2PolarAbs`, `P2AnalyticL2Polar`, `Polar2`, `Polar3`, `Polar4` | polar factor via a spectral positive root (no CFC for real Hilbert operators); `ℓ²(p_D)` realised as `ℝ^{D+1}` via `q ↦ √p_D q`; `G_c` defined as the linear extension on the `J_n` basis (the pointwise characterisation for general `φ` is not formalised); whitening stated on the basis, no operator-level `𝖧₀`/`L̂`; the partial-isometry remark for the unrestricted `C_D` not formalised |

Not formalised in the analytic half: `L²` completeness of the Wigner modes; rationality in `δ` of `s_r` and the convergence domains and exact radii (`rem:exactradii`);
`thm:3jNNLO` and the `6j` degree `-4` term, the Gaunt `N⁻⁴` term,  the all-order local calculus (`thm:3jallorderlocal`, `thm:6jallorderlocal`);
the expansion halves of `prop:3junique` and `prop:unique`; the all-chamber Wigner form `d^f_{nm} = k_{6j} W P̂` for 6j; DLMF 34.5.3; the bridge to Physlib's abstract `sixJ`.

## Asymptotics and Gamma ratios (`FormalResearch/Asymptotics/`, `FormalResearch/Special/GammaRatio.lean`)

All theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

| Statement | Lean |
|---|---|
| Uniform asymptotic expansion, uniform in `z ∈ K` (`IsBigO` over `𝓟 K ×ˢ l`); lattice version | `HasUniformExpansion`, `HasUniformExpansionOn`, `hasUniformExpansion_iff` |
| Algebra: sums, scalars, Cauchy products, restriction, composition, even expansions, coefficient uniqueness, leading term `~` | `HasExpansionAlong.add/smul/mul`, `.of_sq`, `.comp_left`, `.comp_index`, `.eq_of_tendsto`, `.isEquivalent_leading` |
| Analytic or smooth germ `G(z,t)` near `K × {0}` gives a uniform expansion with Taylor coefficients | `hasUniformExpansion_of_analytic`, `hasUniformExpansionOn_of_contDiffOn`, `taylor_uniform` (in `Asymptotics/TaylorUniform.lean`) |
| P2 `thm:3jeven` as a `HasUniformExpansionOn` statement on the physical grid | `Phi3j_hasUniformExpansionOn` |
| `log Γ(x+a) − log Γ(x+b) = (a−b) log x + Σ_{k≤K} c_k x^{-k} + O(x^{-K-1})`, with `c_k` from Bernoulli polynomials (DLMF 5.11.13) | `logGamma_sub_expansion`, `gammaRatioCoeff` |
| `Γ(x+a)/Γ(x+b) ~ x^{a−b}`, plus the two-term form | `gamma_ratio_isEquivalent`, `gamma_ratio_two_term` |
| Expansion of the P2 central products `Ct` | `Ct_log_expansion`, `Ct_log_expansion_two` |

Third-party input: the Euler–Maclaurin formula and the Stirling series for `log Γ` (`log_gamma_em`), vendored without modification from `girving/interval` (Apache-2.0). Location: `ThirdParty/interval/`; see its `NOTICE.md`.

## Next source-authorized finite targets

At the current handoff, the cleanest exact candidates are:

1. QI-D T33 exceptional F4 facet representative certificate;
2. QI-D T33 E6/F4 A2 envelope-to-quartic reduction;
3. QI-A T07 finite coding/guessing lemmas with faithful operational hypotheses;
4. the general type-D support/Procrustes bridge if sufficient real-linear-algebra infrastructure is developed.

QI-D T48 and the QI-B B4 flagship remain open research problems, not current theorem-completion targets.

### Branch `paper-e-ah6`: the global joint scalar majorant (AH-6)

`lem:seven-joint-scalar-majorant` (`joint_entropy_analytic_proof.tex`, `sec:seven-joint-analytic-proof`; verifier
`verify_seven_entropy_joint_majorant.py`): for the explicit degree-five polynomial `H(λ,μ) = P(e) + v A(e) + v² B(e)`
(`e = 4(λ+μ)`, `v = 16(λ-μ)²`; in nats, i.e. the paper's coefficients times `ln 2`) at `x = x_*`, `H ≥ (f(λ)+f(μ))/2` for all
`λ, μ ≥ 0`. Kernel-only: `#print axioms` of every headline theorem is `[propext, Classical.choice, Quot.sound]`
(`cert_ok`: `[propext]`); no `native_decide`, no `sorry`. All modules are `FormalResearch/FourQubitEntropy/AH6*.lean`, imported by
`FormalResearch.lean`.

Headline theorems (`AH6Final.lean`):
- `AH6.joint_scalar_majorant (hb : InBracket x) (cap) : ScalarMajorant (polyH degFive (jointCoef x)) cap`: the lemma for every
  `cap` (so the `497/1000` cap of the earlier reduction is not needed). `jointCoef x` is the explicit table `hcoef` of the 21
  coefficients `h_{kl}` (`AH6Coef.lean`, `polyH_jointCoef` is the identity with `H`). `InBracket x` is
  `XLO/10⁴⁵ ≤ x ≤ (XLO+1)/10⁴⁵`; `bracket_of_root` shows that every real root of `2³²(1-2x)¹⁵ = 3⁸(1+8x)⁸(1+28x)⁷` lies in it.
- `AH6.seven_entropy_max_reduction_joint (hPB : SevenPurityBound)`: with `x_*` the maximiser of the family entropy `E3`, the
  final reduction of `thm:seven-entropy-global-maximum` has `JointMajorantBound` for the explicit `jointP5 degFive (jointCoef x_*)`
  discharged. Remaining hypotheses: `SevenPurityBound` (`π₃ ≥ 121/917`, the separate global purity hypothesis) and the localized
  bound `LocalizedBound (jointP5 degFive (jointCoef x_*)) (E₃ x_*)` (E7-1, not formalized). The SC-2 witness is proved.

Proof structure (paper labels):
- Stieltjes remainder and Jensen (`eq:seven-joint-stieltjes`, `eq:seven-joint-kernel-jensen`): `AH6Newton` (Newton form of the
  quintic Hermite interpolant `P` on the double nodes `8c, 8a, 8d`, divided-difference tableau and its remainder for `1/(ρt+σ)`),
  `AH6Stieltjes` (`kap_remainder`), `AH6StieltjesInt` (`-t ln t = ∫₀¹ t(1-t)/(t+(1-t)r) dr`, a finite-interval form of the paper's
  integral over `[0,∞)` after `s = 8r/(1-r)`; `hermite_stieltjes`: `P - g = q² K̃`), `AH6Jensen` (`jensen_kint`), `AH6Kmin`
  (`kmin`: `k₀ q² ≤ (P - g) L`, with the mean `c` identified with `γ = -K'(e₀)/K(e₀)` by Fermat).
- Binary correction (`eq:seven-joint-binary-minorant`): `AH6Binary` (`avg_identity`, `phiB_hasSum`, `phiB_minorant`: the tangent
  inequality termwise on the power series of `Φ`, with the series values `Φ(1/9)`, `Φ'(1/9)`; for `|s| < 1`, the endpoint `z = 1` is
  covered by continuity).
- Cubic and discriminant (`eq:seven-joint-discriminant`): `AH6Cubic` (`cubic_nonneg`: negative discriminant, `a > 0`, `d ≥ 0` give
  `p ≥ 0` on `[0,∞)`), `AH6Flat` (`R_flat`: `R(e₀) = R'(e₀) = 0` from the double root and `F_e = 0`), `AH6Contact`
  (`contact_algebra`: the three contact identities as exact rational-function identities), `AH6Assembly` (`majorant_all`, including
  the continuity argument for `e = e₀` and the closed quadrant).
- Finite checks (AH-6a/b/c): `AH6Ball` (fixed-point ball arithmetic with a validity flag: `Enc.add/mul/neg/inv`), `AH6Poly`
  (coefficient-list polynomials generic in the arithmetic: `evalL`, `derL`, synthetic division `dl`, Taylor shift, Möbius/Bernstein
  transform `mob`; enclosure lemmas and the positivity lemmas `pos_on_interval`, `pos_on_tail`), `AH6Model` (the whole computation of
  the verifier written once, in four stages), `AH6Enc` (enclosure of every stage), `AH6Logs` (`ln` by the `atanh` series with a
  rigorous tail), `AH6Cert` (`cert_ok : finalCheck parB = true`, by `decide +kernel`), `AH6Sound` (`cert_sound`: the facts
  `k₀ > 0`, `0 < γ`, `γ e₀ < 1`, `η₃ > 0`, distinct nodes and `Π(e) > 0` for all `e ≥ 0`), `AH6Joint` (`R_factor`,
  `kmin_model`, `joint_majorant`).

Differences from the paper: (i) the finite certificate is the paper's one (four rows: Bernstein coefficients on `[0,3/4]`, `[3/4,1]`,
`[1,5/4]` and Taylor coefficients at `5/4`, all 19 positive) but evaluated in integer ball arithmetic (`SC = 2^192`, parameters
`x` in a bracket of width `10⁻⁴⁵`, logs to about `10⁻⁵⁶`) instead of dyadic intervals with `x` bisected; the factor `(e-e₀)²` of `R` is
proved exactly (`R_flat`) instead of being checked by a remainder that contains zero; (ii) the Stieltjes integral is over `[0,1]`
(above); (iii) `Φ(z) ≥ cubic` is proved on `z ∈ [0,1)` (`|s| < 1`), and the endpoint is covered by continuity of the majorant;
(iv) everything is in nats.

Machine requirements (4 cores, 15 GB RAM; one `lake env lean` per file, wall time and peak resident size, which includes about
6.3 GB of memory-mapped `.olean` files; measured with `getrusage`): the certificate `AH6Cert` (kernel evaluation of the whole
computation, about 10⁵ big-integer operations) takes 11 s / 6.9 GB; `AH6Assembly` 22 s, `AH6Flat` 17 s, `AH6Cubic` 16 s,
`AH6Joint` 13 s, `AH6Final` 19 s (each at most 6.9 GB); the remaining AH6 files take 7-12 s and 6.7-6.8 GB each. No piece needs
splitting: the finite check is a single `decide +kernel` of a closed `Bool` (an earlier version with `rfl` on symbolic lists made
the elaborator unfold the list operations; they are now `irreducible` for the elaborator, which the kernel ignores).
Negative tests (a literal corrupted, then restored): reducing the number of `atanh` terms of `ln 2` from 60 to 6, or moving the bracket
of `x` by `3·10⁻³`, makes `decide +kernel` fail. (The certificate is not sensitive to a shift of `x` below `10⁻⁵`; the exactness of
the double root is proved symbolically, not by the numerical check.)

### Branch `paper-e-ah6`: sharp critical-state orbit stability (`thm:fqe-critical-orbit-sharp`)

Sources: `critical_orbit_stability.tex` (proof), `lu_orbit_stability.tex` (statement, `eq:fqe-critical-fidelity`,
`eq:fqe-critical-distance`, `eq:fqe-critical-entropy`), verifier `verify_m4_critical_orbit_overlap.py` (CO-1, CO-2, CO-3). All modules
`FormalResearch/FourQubitEntropy/CriticalOrbit*.lean`, imported by `FormalResearch.lean`; no `sorry`, no `native_decide`, no new
axioms; `#print axioms` of every theorem below is `[propext, Classical.choice, Quot.sound]`. No numerical certificate is used: the
paper's CO-2 is proved analytically (polynomial identities by `ring`, inequalities by `nlinarith`/`linarith` from the paper's
intermediate bounds), and the finite tables (the permutations of the twelve cut probabilities and the closure of the 32
representatives) are checked case by case by `ring`.

Definitions (`CriticalOrbitPhi.lean`): `InOrbit χ := LUEquiv M4 χ ∨ LUEquiv (conj M4) χ`
(`SU(2)` replaced by `U(2)`, which changes `χ` by a phase only); `Phi ψ := sSup {|⟨ψ,χ⟩|² : χ ∈ 𝓜}` (`ip` of
`PaperEGenConvexRoofEq`); `dist2 ψ := 2 - 2 √Φ`. `etaV a`, `a : Fin 32`, are the 32 representatives `𝓗`
(`η_i = 1/√2`, `η_j = ε_j i/√6`); `qH a v = |⟨G(η_a), G(v)⟩|²` is `(Aq + 2√3 Cq)/6`.

Headline theorems (`CriticalOrbitSharp.lean`, `CriticalOrbitMain.lean`):
- `critical_orbit_sharp` (for `normSqPsi ψ = 1`, `blochSq ψ = 0`): `Q ≥ max{1-Φ, 3/2-2Φ}` (`critical_fidelity`),
  `Q ≥ ((2+√2)/4) d²` (`critical_distance`), `δ ≥ k (max{1-Φ,3/2-2Φ} + 5τ/2)` (`critical_entropy_fidelity`) and
  `δ ≥ k (((2+√2)/4) d² + 5τ/2)` (`critical_entropy_distance`, through the existing `entropy_gap_critical_distance`, whose `d2`
  hypothesis is thereby discharged for critical states). The only hypothesis is `hglob : Φ ≥ 1/2 → Q ≥ 1 - Φ`, the all-state
  comparison `thm:fqe-global-overlap`, used only when `Φ ≥ 1/2` (there `3/2-2Φ ≤ 1-Φ`) and discharged by `GO.globalOverlap_all`.
- `bell_product_sharp`: for the Bell-pair product `G(e₀)` (`Gv_e0_apply`: `|Φ⁺⟩₁₂ ⊗ |Φ⁺⟩₃₄`), `Q = Φ = 1/2`, `d² = 2 - √2`, so
  `Q = 1-Φ = 3/2-2Φ = ((2+√2)/4) d²`; both constants are optimal. This uses the upper bound `Phi_Gv_le`.
- `Phi_eq_max` (`CriticalOrbitUpper.lean`): for a critical unit state `ψ ≃ G(v)`, `Φ(ψ) = max_a qH a v`, attained at a representative
  (`eq:fqe-signed-diagonal-overlap` and the 32 representatives). `Phi_Gv_le`: `Φ(G(v)) ≤ B` if `qH a v ≤ B` for all `a`. Proof: every
  orbit element is `(a⊗b⊗c⊗d) G(η_p)` (`exists_M4_conj`: `conj G(v) = G(conj v)` and `conj η₀ = η₇`), its magic coordinates are
  `rc O₁ diag(s η) (rc O₂)ᵀ` with real orthogonal `O₁, O₂` (`coord_localApply`, from `exists_phase_real`), the overlap is `s Σ conj(v_i) η_k O₁_{ik} O₂_{ik}`
  and `sbirk` (`CriticalOrbitBirkhoff.lean`: `|O₁O₂| ≤ (O₁²+O₂²)/2`, entrywise squares doubly stochastic, Birkhoff's theorem for a linear
  functional) bounds it by signed permutation sums; each of these is a representative overlap (`signed_perm`, `exists_a`).
  `Phi_LUEquiv`: `Φ` is local-unitary invariant. `Phi_ge_quarter`: `Φ ≥ 1/4` (frame identity `sum_qH`: `Σ_a qH a v = 8 ‖v‖²`).

Proof of the analytic core (CO-1, CO-2; `Q_lower` in `CriticalOrbitNormal.lean`, `core_real` in `CriticalOrbitReal.lean`):
`Q_lower`: for a unit `v` with `qH a v ≤ Φ ≤ 1/2` for all `a`, `Qv v ≥ 3/2 - 2Φ`, where `Qv = 18 N P - 12 T - 13 N³` of the twelve cut
probabilities `pr v` (`|v_k|²`, `|(H₊v)_k|²`, `|(H₋v)_k|²`; `sexticQ_Gv : sexticQ (Gv v) = Qv v`).
- Symmetries (`CriticalOrbitPr.lean`, `CriticalOrbitH.lean`, `CriticalOrbitNormal.lean`): `Rel v u` (same norm, the twelve probabilities
  permuted, every overlap with 𝓗 of `u` an overlap of `v`) holds for `H₊`, `H₋` (`rel_wp`, `rel_wm`), the swaps of coordinate 0 with `i`
  (`rel_swap1..3`), coordinate sign flips (`rel_flip1..3`) and unit phases (`rel_smul`); `normalize` brings a unit vector to
  `v₀ = r > 0`, `Im v_j ≥ 0`, `p₀` the largest of the twelve probabilities.
- Three-term identity (`CriticalOrbitIdentity.lean`, `eq:fqe-critical-three-term`): `Qv_three_term`, exact, modulo the four `3×3` Gram minors of
  the real 2-vectors `(Re v_i, Im v_i)` (`gram3`).
- `core_real` (CO-2): with the paper's chain `r₀ ≥ 3/5`, `S_x ≤ r₀`, `2 s₂ ≤ (2r₀-1)²`, `q₄ ≤ (2r₀-1)⁴/4` (`core_constraints`) and the decoupled
  bound `𝒴 ≥ 0` (AM-GM) and `𝒳 ≥ 0` (square on `[19/25,1]`; concave `P₁`, `P₂` on `[3/5,16/25]`, `[16/25,19/25]`: `X_nonneg`):
  `Q + 2Φ_im - 3/2 ≥ 0`, `Φ_im = (r₀/√2 + S_y/√6)² ≤ qH 0 u ≤ Φ`.
- Corollary `critical_distance`: `x = √Φ ∈ [1/2, 1]`; `x ≥ 1/√2` uses `Q ≥ 1-x²`, otherwise `3/2-2x² - 2c(1-x) = 2(1/√2-x)(x-(2-√2)/4) ≥ 0`.

Differences from the paper: (i) `Φ` is an `sSup` over the orbit set rather than a `max` (attainment is not used; `Phi_eq_max` shows it is attained among
the 32 representatives); (ii) `Q ≥ 1-Φ` is the explicit hypothesis `hglob` instead of the paper's input `thm:fqe-global-overlap`;
(iii) the proof of the `Φ ≤ 1/2` branch needs only `Φ ≥ qH a v`, i.e. only that `G(η_a) ∈ 𝓜` (`orbit_etaV`, by `LU_M4_of_caseC`); the equality
`Φ = Φ_𝓗` (signed Birkhoff) is needed only for `bell_product_sharp` and for `Phi_eq_max`; (iv) `conj`-orbit handling: `exists_M4_conj` shows that
both `M₄` and `conj M₄` are local unitary images of some `G(η)`, `η ∈ 𝓗`, by `conj G(η₀) = G(η₇)`.

Formalized later: the null-critical refinement `eq:fqe-null-critical-sharp` (`CO.null_critical_sharp`,
`PaperEGapNullCritical.lean`) and `thm:fqe-global-overlap` (`GO.globalOverlap_all`). Not formalized: `thm:fqe-p1-sharp` (`C_*`)
and `thm:sup-null-family` for `θ > 0`.

Machine requirements (one `lake env lean` per file, wall time and peak resident size, which includes about 6.7 GB of memory-mapped
`.olean` files; measured with `getrusage`): `CriticalOrbitReal` 22-48 s / 6.9-7.0 GB (the real inequality, split into many lemmas to avoid
timeouts), `CriticalOrbitH` 62 s / 7.7 GB (eight 32-case closure tables, `maxHeartbeats` raised), `CriticalOrbitPr` 27 s / 7.0 GB,
`CriticalOrbitIdentity` 18 s / 7.1 GB (an unsplit degree-six `ring` needed 10.3 GB and 70 s, so the identity is factored through the
Gram minors), `CriticalOrbitPhi` 17 s, `CriticalOrbitUpper` 16 s, `CriticalOrbitSharp` 15 s, the others 8-11 s (each at most 7.0 GB).
Negative tests (a literal corrupted, then restored): changing the first entry of the `wp` closure table `17 → 16`
(`CriticalOrbitH.lean`) or the first two entries of the permutation `pr_wp` (`CriticalOrbitPr.lean`) makes `ring` fail.

### Branch `paper-e-single-crossing`: optimality of `7/8`, the Rényi single crossing and order transfer

New modules (all `FormalResearch/FourQubitEntropy/`, imported by `FormalResearch.lean`; no `sorry`, no `native_decide`, no new axioms;
`#print axioms` of every headline theorem below is `[propext, Classical.choice, Quot.sound]`).

- `thm:fqe-general-envelope`, optimality of the coefficient `7/8` (check tag ESH; `EnvelopeCoefficientSharp.lean`):
  `general_envelope_coeff_sharp`: for every `C > 7/8` there is a unit state (on the GHZ family `c|0000⟩ + s|1111⟩`, small
  `τ = 4c²s²`) with `F < (3/4 + Cτ/(1+√τ)) W₁ + τ − τ^{3/2}`; `general_envelope_coeff_iff`: that inequality holds for all unit
  states iff `C ≤ 7/8` (the direction `⇐` is `general_envelope_unit` with `W₁ ≥ 0`). Exact values from the definitions of
  `Statement.lean`: `ghz_tau`, `ghz_blochSq_unit` (`W₁ = 4(1−τ)`), `ghz_sexticF` (`F = 3 + 3τ/2`), `ghz_slack` (slack
  `(7/2 − 4C) τ + (1 + 4C) τ^{3/2}`).
- `lem:fqe-renyi-single-crossing` (SX; `RenyiSingleCrossing.lean`, `single_crossing_statement`): for every `q > 1` and every four-point
  probability vector `l`, `v_q(l) − v_q(σ) ≤ κ_q (u_q(l) − u_q(σ))`, with equality only for permutations of `σ = (1/2,1/6,1/6,1/6)`
  (`u_q = ln Σ lᵢ^q`, `v_q = Σ lᵢ^q ln lᵢ / Σ lᵢ^q`, `κ_q = 1/q + ln 3/sinh((q−1) ln 3)`; `sxU`, `sxV`, `sxKappa`; `0^q ln 0 = 0`
  from `Real.log 0 = 0`). The paper's proof is formalised: compactness of the simplex and continuity of `φ = v_q − κ_q u_q`
  (`isCompact_simplex4`, `sxPhiVec_continuousOn`); any maximiser has full support (`IsSXMax.pos`), satisfies the Lagrange condition
  `g(mᵢ) = g(mⱼ)` with common value `−βZ` (`IsSXMax.lagrange`, `IsSXMax.gval`; `RenyiSingleCrossingVar.lean` has the first variation
  `sxPF_hasDerivAt` and the right derivative `sxPF_hasDerivWithinAt_zero` at a zero coordinate); Rolle for `g` (`sxB_of_sxG_eq`);
  two equal coordinates with positive bracket are excluded (`IsSXMax.second_variation`); then `IsSXMax.isHsPerm`: every maximiser is a
  permutation of `σ`. The one-large family `φ(a,b,b,b) = Φ(ln(a/b)) ≤ φ(σ)`, equality only at `a/b = 3`, is
  `RenyiSingleCrossingFamily.lean` (`sxPhiVec_family`, `sxD_eq`, `sxR_eq` (the hyperbolic identity (SR), with `tanh((z−L)/2) =
  (e^z−3)/(e^z+3)`), `sxPhi_strictMonoOn`, `sxPhi_strictAntiOn`, `sxFamily_le`, `sxFamily_eq`).
  Differences from the paper: the second variation `2g'(a)/Z > 0` is replaced by strict monotonicity of `g_{C_τ}` on `[a−τ, a+τ]` for
  small `τ > 0` (continuity of the Lagrange constant `C_τ`), so no second derivative is taken; the uniform vector is the case `z = 0` of
  the family (strictly below `z = ln 3`).
- `cor:fqe-renyi-order-transfer` (`RenyiOrderTransfer.lean`, hypothesis `SingleCrossingStatement`; unconditional instances in
  `RenyiSingleCrossing.lean`): `renyiG_monotoneOn_all`, `renyiG_strictMonoOn_all` (`G_l(q) = (q−1)(H_q(l) − H_q(σ)) /
  (q tanh((q−1) ln 3/2))` is nondecreasing on `(1,∞)`, strictly unless `l` is a permutation of `σ`; proof via
  `N_l = (u_q(l) − u_q(σ))/m(q)`, `m(q) = q tanh(...)`, `m' = κ m` (`renyiM_hasDerivAt`) and `N_l' = (v − v_σ − κ U)/m ≤ 0`);
  `renyi_order_transfer_all` (three four-point spectra, `1 < q < q₁`: `E_{q₁} ≤ h_{q₁} → E_q ≤ h_q`, the strict version, and
  `E_{q₁} ≤ h_{q₁}`, `E_q = h_q` force all three to be permutations of `σ`); `meanRenyi_order_transfer`: the same for the three cut
  spectra of a unit four-qubit vector (`meanRenyi`, `hsRenyi`). Here `H_q = renyiSpec`, `E_q` the mean of three of them.
- Docstring sync: the crossing bracket of `RenyiCrossing.lean` is check tag RA-4; `PaperECriticalZero{Orbits,Set,Alg}.lean` record that
  `moment_zeros` formalises the supplement's second proof of `prop:fqe-moment-zeros` (weighted-variance identity (Z), equations (ZE),
  `sec:sup-sextic-zeros`), not the paper's critical-envelope proof.
- Audit (no change): no module of `FormalResearch/FourQubitEntropy/` cites a TeX label that is absent from `QIprojects` (checked for all
  `thm|prop|lem|cor|def|rem|conj|sec|eq:` labels), so nothing was deleted as dead.

Machine requirements: each new module compiles by `lake build FormalResearch.FourQubitEntropy.<Module>` in 8-20 s (about 6.5 GB, mostly
memory-mapped `.olean` files); `EnvelopeCoefficientSharp` 18 s.

### Branch `paper-e-envelope-equality`: Paper E equality cases and remaining gaps

All modules below build with no `sorry`, `native_decide` or new axiom; each headline has a `#print axioms` guard
(`propext`, `Classical.choice`, `Quot.sound`).

- `thm:fqe-general-envelope`, complete equality: `envelope_equality_iff` (`EnvelopeEqualityClass.lean`): for unit `ψ`,
  `F = (3/4)W₁ + τ − τ^{3/2}` iff `IsProduct ψ ∨ CritEqFamily ψ` (`ψ ≃ G(v)` with `Θ = O(κI + (1−κ)ssᵀ)`, `κ = √τ`, `O` one of the
  twelve signed cyclic permutations with sign product `−1`, `s ∈ {±1}³/√3`); `critical_envelope_eq_iff_vector`,
  `critEqFamily_exists`, `critEqFamily_endpoints`. The `τ = 0`, `W₁ > 0` zero set of `H`: `H_zero_product`
  (`EnvelopeProductZero.lean`); `product_values`. Homogeneous `(GE)` for every nonzero vector: `general_envelope_homog`
  (`EnvelopeHomogeneous.lean`).
- `prop:fqe-critical-envelope` in full (`EnvelopeCriticalClass.lean`, with `EnvelopeTheta`, `EnvelopePermCore/Real/Class`):
  `critical_closed_form` (`F = 1/2 + 7τ/4 + 9 perm Θ/4`), `critical_envelope_perm`, `critical_envelope_eq_iff`,
  `critical_purity` (`P = 1 + τ/2`), `critical_moment_envelope` and `critical_moment_envelope_attained` (every `P ∈ [1,3/2]`);
  matrix core `perm_class`, `main_Os`.
- `prop:fqe-majorant`, equality under the paper's hypotheses (`a > 0`, `b + 17a/12 < 0`, no strict majorisation):
  `majorant_eq_iff_of_pos` (`MajorantEq.lean`).
- `lem:fqe-renyi-grouping`, `prop:fqe-cubic-bound`, necessity of `q_b` (`PaperECriticalRenyiThreshold.lean`): `renyi_binary_iff`,
  `renyi_cubic_iff` (`0 < q ≠ 1`: the bound holds on the whole simplex iff `q ≥ q_b`), `renyi_binary_eq_iff_ge` (equality cases
  for every `q ≥ q_b`), `shannon_binary_violation` (`q = 1`), `qb_bounds` (`3/2 < q_b < 313/200`), `rb_bounds`, `qb_div`.
- `prop:fqe-two-flat-rigidity` (`PaperETwoFlatTF.lean`, `PaperETwoFlatEq.lean`): `two_flat_TF_12/13/14` (both inequalities of
  `(TF)` for an ordered spectrum with `λ₁ ≥ 1/2`), `two_flat_eq_iff_12/13/14` (critical-locus equality: opposite phases),
  `two_flat_sharp_critical`, `two_flat_sharp_noncritical`, `tau_eq_iff`. (QF) is `PaperECritical.two_flat_QF`
  (`PaperEGapTwoFlatQF.lean`).
- `lem:fqe-real-gram`, rectangular `m × n` case: `real_gram_rect` (`PaperECriticalRealGramRect.lean`).
- `lem:fqe-isospectral-overlap`, rectangular case and attainment: `isospectral_overlap_rect`, `isospectral_overlap_schmidt`,
  `isospectral_overlap_attained` (`IsospectralOverlapRect.lean`).
- Genuine orbit distance (`PaperEOrbitDistance.lean`, namespace `OD`): `InM` (the paper's set of LU images of `M₄`, `conj M₄`
  with phase), `orbitDist` (infimum of Hilbert-space distances, attained: `orbitDist_attained`; `Phi_attained`),
  `orbitDist_sq` (`d² = 2 − 2√Φ`), `orbitDist_sq_eq_dist2`, `critical_orbit_sharp_dist`, `entropy_gap_critical_orbit`.
  `lem:fqe-hs-fidelity-floor`: `fidelity_floor` (`Φ ≥ (1+√τ)/6`, `PaperEFidelityFloor.lean`); hence, with
  `thm:fqe-global-overlap` (`GlobalOverlap ψ : 1 − Φ ≤ Q`, proved as `GO.globalOverlap_all`; the `_all` forms are unconditional) as the only hypothesis:
  `entropy_gap_orbit_stability_dist_of_overlap` (`thm:fqe-orbit-stability`, global part), `majorant_gap_orbit_of_overlap`,
  `tsallis_gap_orbit_of_overlap` (`cor:fqe-orbit-spectral`), `overlap_ge_dist_tau`, `orbitDist_sq_le_Q_tau`,
  `entropy_gap_dist_tau`, `orbitDist_sq_le_tau`. Not formalised: the local-radius clauses (`d ≤ 1/20`, `d ≤ 2⁻¹⁰`); the GHZ
  attainment of the fidelity floor is `fidelity_floor_ghz_attained`.
- `lem:seven-joint-scalar-majorant`, equality set: `joint_scalar_majorant_eq_iff`, `joint_scalar_majorant_full`,
  `joint_majorant_contact` (`AH6Equality.lean`).

### Branch `paper-e-renyi-full`: the Rényi envelope above one (`cor:fqe-renyi-gw`, `q > 1`)

**Final headline** (`RenyiFullHeadlineQK.lean`): `renyi_envelope_above_one_QK (hQK : QuadraticVarianceBound)` — `E_q ≤ max(h_q, 5/3)` for every unit
pure four-qubit vector and every `q > 1`, with the equality cases below; it is `renyi_envelope_above_one` with all five per-spectrum certificates
proved except QK (`hsSupporting`, `rationalDual_of_heads smallHeadDual largeHeadDual`, `cappedCubic`, `clusterSliver`).  The only hypothesis is
`QuadraticVarianceBound` (QK, `thm:fqe-quadratic-variance`, a corollary in the paper of the certified sharp bound QV).
**QV form** (`RenyiFullHeadlineQV.lean`): `quadraticVarianceBound_of_sharp : SharpQuadraticVarianceBound → QuadraticVarianceBound`
(the corollary step of `thm:fqe-quadratic-variance`: on `P ≤ 3/2` the QK defect exceeds the QV defect by `3(P-1)(3/2-P)`, above `3/2` the
purity box `p_j ∈ [1/4,1]` suffices; scalar core `qk_of_qv_scalar`), and `renyi_envelope_above_one_QV (hQV : SharpQuadraticVarianceBound)`,
the same envelope assuming only QV (`thm:fqe-sharp-quadratic-variance`); QV itself is proved in `QVCheck/Unconditional.lean`
(section *`thm:fqe-sharp-quadratic-variance` (QV)* below), giving `renyi_envelope_above_one_unconditional`.

New modules `FormalResearch/FourQubitEntropy/RenyiFull*.lean` (namespace `FormalResearch.FourQubitEntropy.RenyiFull`, imported by
`FormalResearch.lean`; no `sorry`, `native_decide` or `axiom`; `#print axioms` of every headline is `[propext, Classical.choice, Quot.sound]`).

- Headline (`RenyiFullHeadline.lean`): `renyi_envelope_above_one`: for a unit pure four-qubit vector and every `q > 1`,
  `meanRenyi q ψ ≤ max (hsRenyi q) (5/3)`; equality with `h_q > 5/3` forces `ψ ≃_{LU} M₄` or `conj M₄`; equality with `h_q < 5/3`
  forces the cut spectra to be the cluster triple `(c₁,c₂,c₂)` (spectral; the (QF) identification of states with two maximally mixed cuts is
  `PaperECritical.two_flat_QF`, below). **Hypotheses (named `Prop`s, paper statements, no axioms):** `QuadraticVarianceBound` (`thm:fqe-quadratic-variance`, QK/QG),
  `HsSupporting` (`lem:fqe-hs-polynomial`), `RationalDual` (`lem:fqe-rational-dual`, RQ), `CappedCubic` (`lem:fqe-capped-cubic`),
  `ClusterSliver` (`lem:fqe-cluster-sliver`). Unconditional: `meanRenyi_cubic_envelope`, `meanRenyi_high_F` (`cor:fqe-renyi-high-f` for states).
- `RenyiFullProps.lean`: statements of the per-spectrum certificates. `RenyiFullDual.lean`: `lem:fqe-dual` (`dual_bound`), corner lemma,
  contact identity (DC), `cubic_envelope` and its equality case. `RenyiFullHZ/Cases/Sliver/Classical.lean`: the case analysis of
  `thm:fqe-renyi-classical` (`classical_of_certificates`, from the six per-spectrum statements). `RenyiFullEnvelope/State/StateEq.lean`:
  `envelope_triple` (from the order transfer), `meanRenyi_envelope`, `hs_triple_LU`.
- Proved here: `lem:fqe-renyi-determinant` (`RenyiFullStieltjes/DetMono/DetChart.lean`: `Zmono`, `lift_det`, `det_reduction`; by a Stieltjes
  representation `x^q·I = ∫ s^{q-2} x²/(x+s) ds`, under which `Σλᵢ^q` depends on the spectrum only through the determinant at fixed `p, t`,
  and a quartic-lifting argument for the maximiser of the determinant), and `lem:fqe-near-uniform-dual` (NU: `RenyiFullTaylor.lean`,
  `RenyiFullNUCells.lean` (5-box Bernstein certificate, about 2.5 min, 7.8 GB), `RenyiFullNU.lean` (about 2 min): `nearUniformDual`).
- Proved on branch `paper-e-renyi-certs`: `lem:fqe-cluster-sliver` (SL, `clusterSliver : ClusterSliver`), following the paper's proof:
  `RenyiFullRpow.lean` (integer-power rpow comparisons, `ln(1-z) ≥ -z-z²/(2(1-z))`, `ln(1+z) ≥ z-z²/2`), `RenyiFullSliverEnt.lean` (`binary_ent` (SE),
  `entS`, `entB` (SH): `H_{q_s}` of the two charts; Taylor `sym_taylor`, `u^{q_s} ≥ (51/50)u^{8/5}`), `RenyiFullSliverCells.lean` (generated by
  `gen_sliver_cells.py`: `slA_*` the four rows of (ST) as 2-variable Bernstein certificates after `κ`/`ε` elimination, `slC_*` the endpoint
  `v = V(u)` polynomial, `slQ_identity` the Hermite minorant `x^8 ≥ Q(x^5)`), `RenyiFullSliverCore.lean` (generated by `gen_sliver_core.py`: `chord`
  concavity in `v`, `end_*`, `core_*`, `coreB_*`, `yL1-3`), `RenyiFullSliverProof.lean` (domain reductions, `clusterSliver`).
- Proved on branch `paper-e-hs`: `lem:fqe-hs-polynomial` (`hsSupporting : HsSupporting`, with its equality clause) and the reusable low-tilt path lemma
  `lem:fqe-low-tilt-reduction`. `RenyiFullDivDiff.lean`: `neg_dd2_ge` (`-[a,b,c]x^r ≥ (r(1-r)/2)((a+b+c)/3)^{r-2}`, the Hermite-Genocchi/Jensen step, proved
  without integrals: `x^r` minus its cubic Taylor polynomial at the mean is concave). `RenyiFullPath.lean`: the generic fixed-purity path engine
  (`hasDerivAt_pathF`, `path_strictMonoOn/AntiOn`). `RenyiFullSlope.lean`: Jensen bound `Z ≤ p^{q-1}`, `ar_bound`, the slope constants (`η > 64/35 > 9/5`,
  `η > 1` via `105^5 < 3·2^32`). `RenyiFullLowTilt.lean`: `lowTilt_chart_strict`, `lowTilt_reduce` (for `3/2 ≤ q ≤ 8/5`, `0 ≤ β ≤ 3/20`, any `α, γ`:
  every chart spectrum has an `(a,b,c,c)` spectrum of the same purity with at least as large `Λ_{(α,β,γ)}`, equal only if it is the same spectrum).
  `RenyiFullHsTilt.lean`: `hsTilt_reduce` (`lem:fqe-hs-tilt`, `q = 8/5`, `p ≤ 9/16`). `RenyiFullTangent.lean`: `tangent_argument` (abstract convex-then-concave
  tangent argument). `RenyiFullHsOne.lean`/`RenyiFullHsConst.lean`: the one-variable inequality `PhiX_le` (HCJ identity `JX_deriv`/`JX_anti`,
  `Q > 0`, `E(x*) = 0`, uniform gap `PhiX_one_lt` from `Real.abs_log_sub_add_sum_range_le`). `RenyiFullHsProof.lean`: `hsSupporting`.

### Branch `paper-e-bq`: `lem:fqe-binary-quartic` at `q_s` and `lem:fqe-capped-cubic` (CG), proved

New modules `FormalResearch/FourQubitEntropy/RenyiFullBQ*.lean`, `RenyiFullCC*.lean`, `RenyiFullCappedCubic.lean`
(same namespace; no `sorry`, `native_decide` or `axiom`; `#print axioms` of every theorem below is `[propext, Classical.choice, Quot.sound]`).  Certificates are generated: `gen_bq_cells.py` (`RenyiFullBQCells.lean`),
`gen_cc_cells.py` (`RenyiFullCCCells.lean`).

- `lem:fqe-binary-quartic` at `q = q_s = 1587/1000` (real-variable proof of `renyi_binary_quartic.tex`, BQ-1..BQ-4):
  `RenyiFullBQOde.lean` (`bqx` = `x(s) = tanh(q artanh s)`, Riccati equation `hasDerivAt_bqx`, `s < x < 1`, rational bound
  `bqx_le_bqU` by monotonicity of `Ψ`, `U - x ≤ s⁷/70`), `RenyiFullBQG.lean` (`f'`, `G`, `G'`, `G'' = -qM/(2s⁵(1-s²)⁴)`, i.e. BQ-1),
  `RenyiFullBQCells.lean` (`bqK_neg`: BQ-3, all 15 Bernstein coefficients of `K(q_s,s)` negative; `bqdM_nonneg`: BQ-4, four `s`-boxes),
  `RenyiFullBQSign.lean` (`bqM_x_neg`, `bqG2_pos`: `G'' > 0`), `RenyiFullBQConv.lean` (`bqG1_pos`: `G' > 0`; `G'(0+) = 0` from the exact
  cancellation `N₁(s,U)Q³ = s⁵(q-1)(1-s²)² NN(s)` and `U - x = O(s⁷)` instead of analyticity), `RenyiFullBQRolle.lean`
  (`divdiff_strictAntiOn`: Rolle argument in place of the Hermite--Genocchi formula), `RenyiFullBQBinary.lean`:
  `bqD_third_pos` (`D_q''' > 0` on `(0,1)`), `bqD_second_strictMonoOn`, `bqA_strictMonoOn` (`A_q` strictly increasing on `(0,1/2)`),
  `binary_quartic_bound` / `binary_quartic_bound_spec` (the quartic bound from an endpoint value).  Not formalised: strict concavity of `A_q`.
- `lem:fqe-capped-cubic`: `cappedCubic : CappedCubic` (`RenyiFullCappedCubic.lean`).  Moment case `p ≤ 21/50`: `RenyiFullCCMoment.lean`
  (`cc_moment`, `cc_log_ge`: concavity of `ln N` in `x` with certificates CC-1/CC-2).  Binary quartics: `RenyiFullCCBinary.lean`
  (`bin_quartic1`, `bin_quartic2`, `bin_cubic`).  Pair charts: `RenyiFullCCPairs.lean` (`renyi_group2`, `entS_cc`, `entB_cc`, weights),
  assembled by `cc_final_ineq`, `cc_pairS`, `cc_pairB`.

### Branch `paper-e-rd`: `lem:fqe-rational-dual` reduced to `lem:fqe-large-head-dual`; `lem:fqe-small-head-dual` proved

The band-`L` multiplier is now `α = aL = 397/100` (`β = 3/20`, `γ = 159/100`; `WL` and the target `WL - 10⁻⁵ = 2507333/1500000` are unchanged since the
minimising corner has `ε = 0`).  `RenyiFullRD.lean`: `SmallHeadDual`, `LargeHeadDual` (named `Prop`s, the two chart bounds of the analytic proof of
`lem:fqe-rational-dual`) and `rationalDual_of_heads : SmallHeadDual → LargeHeadDual → RationalDual` (`lam_reduce_abcc` at `q_s`, `β = 3/20`, and the purity
cap `p ≤ 49/75 ⇒ a ≤ 4/5`).  `RenyiFullSmallHead.lean`: `smallHeadDual : SmallHeadDual` (`lem:fqe-small-head-dual`, `Λ_θ ≤ 8023/4800` for `a ≤ 1/2`),
from `RenyiFullSHJensen` (head/tail Jensen, `sh_jensen`), `RenyiFullSHBin` (`binH_le_of_exp`), `RenyiFullSHD` (`bqD_chord`: `D_q` concave on `[0,1/9]`, so
`D_q(z) ≥ 9 D_q(1/9) z`), `RenyiFullSHNodes` (generated by `gen_sh_nodes.py`: `A_q(u_i) ≥ a_i` at seven nodes), `RenyiFullSHSmall` (deficit (SHD)),
`RenyiFullSHPoly` (generated by `gen_sh_poly.py`: the quartic bounds `shQ_le_k`), `RenyiFullSHTail` (`sh_small_tail`, `u ≤ 1/4`),
`RenyiFullSHLargeCells` (generated by `gen_sh_large.py`: one Bernstein cell of bidegree `(7,8)`), `RenyiFullSHLarge` (`sh_large_entropy`, reusing `nu_taylor_sum`),
`RenyiFullSHLargeTail` (`sh_large_tail`, `u ≥ 1/4`).  Deviations from the paper: the concavity of `A_q` is replaced by a staircase of node values using only
`bqA_strictMonoOn`; the Taylor bound of `D_q` at 0 by the chord bound; the concavity-in-`x` and tangent-square argument of the large tail by one Bernstein cell.

### Branch `paper-e-lh`: `lem:fqe-large-head-curvature` and `lem:fqe-large-head-dual` proved (`largeHeadDual`)

`RenyiFullLargeHead.lean`: `largeHeadDual : LargeHeadDual` (`Λ_θ < 2507333/1500000` on the ordered chart `(a,b,c,c)`, `1/2 ≤ a ≤ 4/5`), via the chart
function `fS z a = h(a, K(z)) + P(a; B(z), C(z))`.  Curvature (`fS3_nonpos`, `lem:fqe-large-head-curvature`, real-variable proof): `RenyiFullLHChain`
(`y = (a^q - K(1-a)^q)/(a^q + K(1-a)^q)`, `y' = 2q(1-y²)/(1-x²)`, derivatives of `ln Z` as rational functions of `(x,y)`, `lhm1..lhm4`, `lhJ`), `RenyiFullLHQuasi`
(`J(·)` is quasi-convex on `[x,1]`: `J'` convex, `J'(x) ≤ 0`), `RenyiFullLHCurv` + generated `RenyiFullLHCurvCells` (`gen_lh_curv.py`; envelopes `ρ² ≤ ρ^q ≤ ρ(1+ρ)/2`
replace the Cauchy-formula endpoint bounds; three degree-12/16/16 Bernstein certificates), `RenyiFullLHKfun` + `RenyiFullLHDefs` (`K'''' > 0`, cubic Hermite minorant
`K_*` at `0,1`, chord bound), generated `RenyiFullLHHalfCells` (`gen_lh_half.py`, the `a = 1/2` polynomial), `RenyiFullLHChart` (`fS3_nonpos`, `fS_le_Qh`).
Hermite sign lemmas by Rolle only: `RenyiFullLHHermite` (`hermite3_nonpos`, `hermite4_nonneg`).  Dual: `RenyiFullLHMono` (`Qfun_anti`: the quadratic
Hermite bound is decreasing in `K` on `[13/25,1]`), `RenyiFullLHKappaData`/`RenyiFullLHKappa` (`kap_le_kfun`, generated by `gen_lh_kappa.py`: `K ≥ κ`, `κ` the 7-digit
rounding of the Hermite interpolant at `3/20, 17/20`), `RenyiFullLHLog` (artanh series enclosures), `RenyiFullLHConst` (generated by `gen_lh_consts.py`: `U, ρ, H₀, H_l`
to `2·10⁻⁸`), `RenyiFullLHApprox` (`(LH2)`: `H0_approx`, `Hl_approx`, `Ha_approx`), `RenyiFullLHFinalCells` (generated by `gen_lh_final.py`: `c₂ ≥ 1/10`,
`4c₀c₂ - c₁² ≥ 3/100` by Bernstein expansions of degree 13 and 26).
Deviations: the monotone-in-`K` step is a derivative argument in `K` (`QD_nonpos`); the error term `e₀(1+t²)` is replaced by `e₀` (`|1-t²| ≤ 1` on the range of `t`);
`κ` has 7-digit coefficients.

### The shared n-qubit library `FormalResearch/NQubit/` (aggregate `FormalResearch.NQubit`)

General `n`-qubit material used by more than one development, with no generated data and no kernel-evaluation checks
(every module builds in well under 30 s).  Namespaces `FormalResearch.NQubit.<Dir>`; `FormalResearch.NQubit` imports all modules.

- `Foundations`: `Ψ n`, `ip`, `nsq`, `rot`, `Θ`, `pauliSU`, and the Pauli average.
- `Entropy/{QuadraticMajorant,PurityEnvelope,PuritySlope}`: the Hermite majorant of `-x ln x`, the entropy envelope `entropy_le_gEnv`
  at fixed purity and the sharp entropy–purity slope (every dimension; see the section below).
- `Pauli/{Weight,Conjugation,Hermitian,GHZ}`: `pauliWeight`, `pexp` (the `pauliSU` expectation, `pauliSU = {1, -iσₓ, -iσ_y, -iσ_z}`, so `pexp` is
  the Pauli expectation up to the phase `(-i)^{pauliWeight}`), `pauliSq`, the weight enumerator `weightEnum`, `tau`, the global parity identities; conjugation
  and time reversal of Pauli expectations; the Hermitian Pauli strings `pauliMat`/`pauliExp`; the GHZ state.
- `Reduced/{Purity,PartialTrace,MeanPurity,Entropy}`: cut purities `swapPurity`/`cutPurity`, `cutPuritySum`, the partial trace `rdm`,
  `meanPurity`/`meanRdmPurity`, `cutEntropyBits`, `meanEntropy`, `meanEntropy_le`.
- `TimeReversal/{Omega,OddSector,OddOverlap,Doubling}`: the branch states and `omegaState`, `oddPur`/`Omean`, the spin-flip overlap `Rspin`, odd-weight selection
  for doubled states and triple purities.
- `Shadow/{Basic,Homogeneous}`: Rains' shadow inequalities `shadow_nonneg` and `shadow_homogeneous`.
- `Graph/{State,CutPurity,F2Rank,CutRankBitmask,MeanPurity,Symmetry}`: `graphState`/`graphStateNorm`, `tau_graphState`, `purity_gsn`, `graphCutRank`, the bitmask rank
  `graphCutRankBits`; `Symmetry`: `graphCutBits_image` (cut ranks are invariant under graph automorphisms) and `sum_rankFn_eq_reps` (a sum over all `k`-subsets of an
  automorphism-invariant function equals the sum over orbit representatives weighted by the orbit sizes, with a data-light list certificate; no data in the library).

- `Graph/Stabilizer`: graph states are stabilizer states. `graphStateNorm_isStabilizerState` (every simple graph, symmetric loop-free `Γ`): `IsStabilizerState (graphStateNorm Γ)`
  with the group `graphStabWords Γ = {pword s (nbr Γ s) | s : Fin n → ZMod 2}` (the words `P_S = ∏_{i∈S} K_i`, `K_i = X_i ∏_{j~i} Z_j`; `graphStabWords_isStabilizerGroup`:
  `2^n` words by injectivity, closure via `pmulW_pword` and `nbr_add`, commutation via the vanishing symplectic form `sum_symp_nbr`), `⟨P⟩² = 1` from `rot_pword_graph`
  (`P_s |G⟩ = c_s |G⟩`, `|c_s| = 1`; entrywise form `pauliSU_letter`) in `pauliSq_graphStateNorm`. Corollaries `weightEnum_graphStateNorm_nat`, `shadowCoeff_graphStateNorm_nat`.
  Axioms `[propext, Classical.choice, Quot.sound]`.

The Paper E modules `SpinFlip*`, `PurityLP*` in `FourQubitEntropy/` import this library; see the sections below for their statements.

### Branch `paper-e-lp`: exact minima of the mean balanced-cut purity (the Rains LP tables), `n ∈ {4,5,6,8,…,12,14,…,18}`

Modules `FormalResearch/FourQubitEntropy/PurityLP*.lean` (namespace `FormalResearch.FourQubitEntropy.PurityLP`) over the shared library `FormalResearch/NQubit/` (namespaces `FormalResearch.NQubit.{Pauli,Reduced,TimeReversal,Shadow,Graph}`; no `sorry`,
`native_decide` or `axiom`; `#print axioms` of every theorem named below is `[propext, Classical.choice, Quot.sound]`).  Source:
`QI/multiqubit_entanglement/seven_qubit_entanglement/even_qubit_purity_minima.tex` (`thm:lptable`, `tab:minima`, `tab:graphs`,
`thm:fourteenfifteen`, `thm:sixteenseventeen`) and `balanced_purity_18.tex` (`thm:eighteen`).  `n = 7` and `n = 13` are out of scope.

**Headline** (`PurityLPMain.lean`, generated by `gen_lp_graphs.py`), for each listed `n`, `k = ⌊n/2⌋`:
`minPurity<n> : IsLeast {x : ℝ | ∃ ψ : Ψ n, nsq ψ = 1 ∧ meanRdmPurity ψ k = x} L_n` with `L_n` the entry of `tab:minima`
(`1/3, 1/4, 1/8, 3/35, 1/14, 1/21, 1/28, 5/224, 331/27456, 1/104, 1/156, 1/208, 7/2288`), where
`meanRdmPurity ψ k = C(n,k)⁻¹ Σ_{|S|=k} Re tr(ρ_S²)` and `ρ_S = rdm ψ S` is the explicit partial trace (`NQubit/Reduced/PartialTrace.lean`).
No hypothesis remains: the shadow inequalities are proved, not assumed.

- Stage 1, `NQubit/Pauli/Hermitian.lean` and `NQubit/Reduced/MeanPurity.lean` (reusing `NQubit/Pauli/Weight`, `Reduced/Purity`,
  `Reduced/PartialTrace`, `TimeReversal/OddSector`): `pauliSq_eq_pauliExp_sq` (`weightEnum` is
  `Σ_{pauliWeight P = j} ⟨ψ|P|ψ⟩²` for the genuine Hermitian Pauli strings `pauliMat`), `weightEnum_zero_of_unit` (`A_0 = 1`),
  `Pauli.sum_weightEnum` (`Σ A_j = 2^n`), `meanRdmPurity_eq_meanPurity`, `meanPurity_eq_lin` (`eq:as`: `a_s = Σ_j C(n-j,s-j) A_j / (2^s C(n,s))`),
  `meanPurity_compl` (`a_s = a_{n-s}`).
- Stage 2, `NQubit/Shadow/Basic.lean`: `shadow_nonneg : 0 ≤ shadowCoeff ψ i` for every `ψ : Ψ n` and `i` (Rains' shadow
  inequalities), `shadowCoeff ψ i` = coefficient of `y^i` in `S(1,y)`, `S(x,y) = Σ_j A_j ((x+3y)/2)^{n-j}((y-x)/2)^j`;
  `NQubit/Shadow/Homogeneous.lean`: `shadow_homogeneous` (`S(x,y) = Σ_i S_i x^{n-i} y^i`, so the coefficient is the paper's);
  `shadowCoeff_eq_lin` (`S_i = Σ_j shQ n i j · A_j`, explicit rational coefficients).  **The proof is not Rains' original:**
  give every qubit a type `τ ∈ {0,1,2,3}` (flip with kernel `ε`, or a marked axis with kernel `Z`, `1`, `X`); the Pauli-completeness
  computation `sum_wloc_pauliSq` gives `Σ_P (∏ w_{tᵢ}(Pᵢ)) ⟨P⟩² = 2^n |β_t|²`, and summing `y^{#nonflip}` over `t` gives
  `(1+3y)^{n-pauliWeight P}(y-1)^{pauliWeight P}` (`sum_over_types`), so `S_i = Σ_{#nonflip(t) = i} |β_t|² ≥ 0`.
- Stage 3, `PurityLPCert.lean` (`lp_bound`: a rational certificate `(L, es, ys)` that passes the decidable `lpCheck` gives
  `L ≤ meanPurity ψ ⌊n/2⌋` for every unit `ψ`), `PurityLPCertData.lean` (generated by `gen_lp_certs.py`: `lpBound<n>`, `decide +kernel`).
  Multipliers for `n ≤ 12` are those found by the exact LP of `verify_balanced_purity_lp_graph_states.py` (the paper's
  script computes them at run time); for `n = 14..18` those printed in the paper's scripts.
- Stage 4: `NQubit/Graph/F2Rank.lean` (`rkF_eq`/`f2rank_eq`: bitmask Gaussian elimination computes `finrank_{𝔽₂}` of the row space),
  `NQubit/Graph/CutPurity.lean` (`purity_gsn : cutPurity (graphStateNorm Γ) S = (1/2)^{rk_2 Γ[S,S^c]}`, `graphCutRank` the `Matrix.rank` of the biadjacency
  matrix; proved from the swap form `swapPurity` via `qf_four`, not by stabiliser counting), `NQubit/Graph/CutRankBitmask.lean` (`graphCutRank_eq_bits`: the
  `Matrix.rank` equals the kernel-computable `graphCutRankBits`), `NQubit/Graph/MeanPurity.lean` (`meanRdmPurity_graphStateNorm`), `PurityLPMaskSum.lean` (the fast kernel route: `maskSum`, a depth-`n` binary recursion over
  cuts stored as `ℕ` bitmasks, `sum_cuts_eq_maskSum`: it equals `Σ_{S ∈ powersetCard k univ} g(graphCutRankBits adj S)` for every `n`, `adj`, `g`;
  `graphCutRankBits_compl`: `rk_2 Γ[S^c,S] = rk_2 Γ[S,S^c]` for a symmetric graph, by `Matrix.rank_transpose`; `sum_cuts_half`: for `n = 2k` the sum over
  all `k`-cuts is twice the sum over the cuts containing the last vertex; `maskSum_split`: one recursion step, used to cut a sum into
  separate `decide +kernel` declarations), `PurityLPRankHist.lean` (`hist_of_packed`: one packed sum `Σ_S 65536^{rk S}` determines the whole rank
  histogram by uniqueness of base-`65536` digits, `rankSum_of_hist`), `PurityLPGraphData{A,B,16,17,18}.lean` (generated by `gen_lp_graphs.py`:
  `adj<n>L`/`adj<n>` (+ `adj<n>_spec`: the stated circulant / edge list), the kernel-checked packed sum `pack<n>`, the **full rank histogram
  `rankHist<n>` (`∀ r, #{S : rk S = r} = c_r`, so also "no other rank")**, `rankSum<n>`, `meanRdmPurity_graph<n>`).
- Deviations from the paper: (i) the proof of the shadow inequalities (above); (ii) `tr ρ_S² = 2^{-rk}` is proved from the swap
  form of the purity rather than quoted from Hein–Eisert–Briegel; (iii) the Pauli weight enumerators and the `2^{18}`-stabiliser
  enumeration of `thm:eighteen`/`rem:ten` are not formalised (they are not needed for the minimum).
- Build cost of the rank sums (sequential builds, one module at a time; peak resident memory in parentheses): `n = 14, 15` (`DataB`) 1 min 40 s (8.4 GB),
  `n = 16` 1 min 37 s (8.7 GB), `n = 17` 5 min 41 s (8.8 GB), `n = 18` 6 min 35 s (9.1 GB) (previously about 8 min, 6 min, 12 min and 29 min with `Finset.powersetCard` unfolding and
  the block decomposition `S ∩ {0,1,2,3}`).  The generated modules set `Elab.async false`: the kernel's cache grows with the cuts evaluated, so
  concurrent `decide +kernel` declarations multiply the peak memory; each leaf declaration evaluates at most about 2000 cuts.
  Rank histograms for **all** `n = 4,…,12,14,…,18` are now kernel-checked (before: only `n ≤ 15`).
- No discrepancy was found in the paper's formulas or tables: every `A_j`, `a_s`, `S_j` formula, all 13 dual certificates and all
  13 rank multisets match the Lean definitions.

### The entropy–purity slope and envelope in every dimension; the ceilings of `tab:fqe-other-n`

Source: `seven_qubit_entropy_compatibility.tex` (`lem:seven-entropy-linear-purity`, `eq:entropy-purity-general-slope`, SP7-5),
`seven_qubit_entropy_global_upper.tex` (`lem:seven-fixed-purity-envelope`, all dimensions), `four_qubit_entropy.tex`
(`tab:fqe-other-n`, verifier `verify_entropy_purity_upper_table.py`, EU-1/EU-2).  No `sorry`, `native_decide` or `axiom`;
`#print axioms` of every theorem named here is `[propext, Classical.choice, Quot.sound]`.  Namespace
`FormalResearch.NQubit.Entropy` unless stated (the shared library `FormalResearch/NQubit/Entropy/`).

- `NQubit/Entropy/PurityEnvelope.lean` (`lem:seven-fixed-purity-envelope`, every `d ≥ 2`): `entropy_le_gEnv`: for a probability vector
  `λ` on a `d`-point set, `∑ -λ ln λ ≤ gEnv d (∑ λ²)`, `gEnv d p` = entropy (nats) of `(t, ((1-t)/(d-1))^{d-1})`,
  `t = spikeWt d p = (1 + √((d-1)(dp-1)))/d`; `entropy_eq_gEnv_iff`: equality iff `λ` is that one-spike spectrum (uniform and
  pure ends included).  The equality case uses the strict Hermite majorant `negMulLog_lt_hermiteMajorant` (proved here; the non-strict Hermite majorant `negMulLog_le_hermiteMajorant` is in `NQubit/Entropy/QuadraticMajorant.lean`).
- `NQubit/Entropy/PuritySlope.lean` (`lem:seven-entropy-linear-purity`, every `d ≥ 3`): `entropy_purity_slope_nats`
  `(d-1) ln(d-1)/(d(d-2)) · (d ∑ λ² - 1) ≤ ln d - ∑ -λ ln λ`; `entropy_purity_slope_bits` `slopeBits d · (d ∑ λ² - 1) ≤
  log₂ d - S`, `slopeBits d = (d-1) log₂(d-1)/(d(d-2))`; `entropy_purity_slope_eq_iff`: equality iff `λ` is uniform or
  `((d-1)/d, (1/[d(d-1)])^{d-1})`.  The one-spike function: `spikeDeficit_ge_sharp` (`m² ln m/(m-1) · r² ≤ F_m(r)` on `[0,1]`, `m > 1`),
  `spikeDeficit_eq_iff` (equality iff `r ∈ {0, (m-1)/m}`), `spikeEnt_eq`.
- The `d = 8` theorems are corollaries with unchanged names and statements: `SevenQubitConseq.entropy_le_g8` (`g8_eq_gEnv`),
  `LinPur.entropy_linear_purity_sharp_nats`, `LinPur.Fsp_ge_sharp` (`Fsp_eq_spikeDeficit`), `LinPur.Gsp_spike`.
- `NQubit/Reduced/Entropy.lean` (namespace `NQubit.Reduced`): `cutEntropyBits ψ S` (von Neumann entropy in bits of `rdm ψ S` from its
  Hermitian eigenvalues), `meanEntropy ψ k = C(n,k)⁻¹ Σ_{|S|=k} cutEntropyBits ψ S`; `meanEntropy_le`: for every unit
  `ψ : Ψ n` and `2 ≤ k ≤ n`, `E_k(ψ) ≤ k - c_{2^k}(2^k π_k(ψ) - 1)` (`π_k = meanRdmPurity ψ k`).  `PurityLPEntropyCeiling.lean` (namespace `PurityLP`), with `minPurity<n>`:
  `entropyCeiling<n>` for `n = 8,9,10,11,12,14,15,16,17,18` (`k = ⌊n/2⌋`) states, for every unit `ψ`,
  `E_k(ψ) ≤ k - c_{2^k}(2^k L_n - 1)` and `E_k(ψ) <` the displayed decimal (`3.9029, 3.9627, 4.9163, 4.9772, 5.9594, 6.9702,
  6.9874, 7.9800, 7.9928, 8.9901`, as exact rationals).  The decimal step bounds `log₂(2^k-1)` below by the `arctanh` series
  (`LinPur.arctanhHi`) and `ln 2 > 0.6931471803`.  Not formalised: whether the table's ceilings are attained (they are upper
  bounds only).
### `thm:fqe-global-overlap` (`Q ≥ 1 − Φ`), the reduction to the 19-coordinate normal slice

Source `global_overlap_certificate.tex` (coverage by the normal slice, positive constraints at a closest point). The
final polynomial certificate (`eq:fqe-global-overlap-sos`) is **not** proved here; the interface it must discharge is
`GO.GOSliceCertificate`. Namespace `FormalResearch.FourQubitEntropy.GO`; every headline theorem has an axiom guard.
- `PaperEGoSlice.lean`: the slice objects, matching `orbit_certificate_polynomials.py` (`sX`, `sY` in the order
  `t u₁u₂u₃ a₁a₂a₃ e₁₂e₁₃e₂₃ b₁₂b₁₃b₂₃ p₁p₂p₃ q₁q₂q₃`, `sN`, `sH0`, `sE`, `sliceQ` = `defects` of the checker, `sliceTarget =
  (Q − n² e)/36`, `sK0`, `sK1`, `sL`, `sB0`, `sHess` = `height_hessian()`), `SliceConstraints`, **`GOSliceCertificate`**
  (`∀ v, SliceConstraints v → 0 ≤ sliceTarget v`), `IsFrame` (a closest point of `𝓜` at `Z_*`), `IsFrame.Phi_eq`,
  `normSqPsi_sState`.
- `PaperEGoSliceOrbit.lean`: `orbit_mem4` (every `e · P Z_* Qᵀ`, `P, Q` real orthogonal of either determinant, is the magic
  matrix of an element of `𝓜`; reflections via `diag(1,−1,−1,−1) Z_* = conj Z_*`), `IsFrame.re_le`, `ip_coord`.
- `PaperEGoSliceGen.lean`: `height_ineqG` (the real height inequality `c(3A₀₀+ΣB_kk)+3s(B₀₀−ΣA_kk) ≤ 3X₀₀+ΣY_kk` at an
  arbitrary frame), `IsFrame.hgt_eq`.
- `PaperEGoSliceConstr.lean`: from `IsFrame (sState v) h`: `K0_psd`, `K1_psd` (Procrustes, `K₀, K₁ ⪰ 0`), `L_psd` (all
  lower-frame matrices `L_{σ₀,σ,c,s} ⪰ 0`), `B0_psd` (from `fidelity_floor`), `IsFrame.e_nonneg`, `IsFrame.rays`,
  `frame_constraints` (assembles `SliceConstraints` from the Hessian hypothesis `FrameHess`).
- `PaperEGoSliceStat.lean`: `stationary_of_frame` (the ten relations of `eq:fqe-slice-stationary`), by rotations and `lin_zero_*`.
- `PaperEGoSliceFrame.lean`: `exists_frame` (every unit state has a closest-point frame with the same `Q`, `Φ`;
  `sexticQ_conj`, `Phi_conj`, `exists_same_class`).
- `PaperEGoSliceMain.lean`, `PaperEGoSliceNormal.lean`: `SliceNormalForm` is **proved** (`sliceNormalForm`:
  `exists_slice_frame`, spectral theorem `exists_so3_diag`, `frame_rotate`, `slice_of_rel`).
- `PaperEGoSliceHess.lean`, `PaperEGoSliceHessQ.lean`: `FrameHess` is **proved** (`frameHess`: the height along the group curve
  `(exp sL, exp sR, phase)` is maximal at `s = 0`; `max_second_order`, `hess_gen`, and the polynomial identity `−F''(0) = wᵀ H w`);
  `sHessExp`/`sHess_eq_exp`: the explicit `10×10` matrix of rational linear forms; `SliceConstraints.t_nonneg`, `.Y3` (`t ≥ 0`, `Y₃ ⪰ 0` from `K₀`). Final theorem
  `globalOverlap_of_slice_cert : GOSliceCertificate → SliceQIdentity → ∀ ψ, normSqPsi ψ = 1 → GlobalOverlap ψ`.
- `PaperEGoSliceQId.lean`, `PaperEGoSliceQId2.lean`, `PaperEGoSliceQId3.lean`: **`SliceQIdentity` is proved** (`sliceQIdentity`).
  `sexticQ_psiZ` is `eq:fqe-global-intrinsic` for the state `ψ_Z` with arbitrary magic matrix `Z`
  (`Q = −4n³ + 27 n tr(ZZ†)² − 18 tr(ZZ†)³ − 18‖ZZᵀZ − (tr ZᵀZ/2)Z‖²`): adjugate route `Q = 5n³ − 36 Σ_cuts tr adj ρ`,
  `tr adj(MM†) = ‖adj M‖²`, the entrywise cubic identities `adj13_eq`, `adj14_eq` (`adj M₁₃ = α₁₃(adj Z, N)`) and
  `Σ|α₁₃|² + Σ|α₁₄|² = ½(‖adj Z‖² + ‖N‖²)` (`quad_identity`); then specialised to `Z = √3 X + iY` (`ZZH_slice`, `re_trace_sq`,
  `re_trace_cube`, `Nf_slice`).
- `PaperEGoSliceFinal.lean`: **`globalOverlap_of_slice : GOSliceCertificate → ∀ ψ, normSqPsi ψ = 1 → GlobalOverlap ψ`** (no other
  hypothesis; axioms `propext`, `Classical.choice`, `Quot.sound`). The certificate itself is discharged, in the frame form
  `GOFrameCertificate`, by the next section.

### `thm:fqe-global-overlap` (`Q ≥ 1 − Φ`) for every unit state (reduction + certificate joined)

Joins the reduction (`PaperEGoSlice*`, section above) and the certificate (`GOProbe/*` with the generated data
`GOData/*`, `gen_go_cert.py`, `GOProbe/MEASUREMENTS.txt`). Namespace `FormalResearch.FourQubitEntropy.GO`.

*Data-independent modules (in the aggregate `FormalResearch`):*
- `GOGlue/PQ.lean`: `PQ d`, rational polynomials of degree `≤ d` (denominator + sparse integer polynomial with packed keys),
  computable `add`, `mul`, `smul`, `sumF`, matrices (`pmul`, `padd`, ...) with `PQ.val` a ring-hom (`val_add`, `val_mul`, ...) and
  `Rel` (entrywise value = a real matrix).
- `GOGlue/Target.lean`: `pTarget` (= `sliceTarget`), `pRem` (= `R_sq + R_ax` of `GOProbe/Remainders.lean`), `pL` (= `sL`),
  with `pTarget_val`, `pRem_val`, `pL_rel` (the slice-side real expressions transcribed in `PQ`).
- `GOGlue/Hess.lean`: `pHess` (= `sHess`, the integer double actions of the generators), `pHess_rel`.
- `GOGlue/Ray.lean`: `ray_exists` (`a = MΠ`, `Π` a rank-one projector ⇒ `a = P e₀e₀ᵀQᵀ`, `a + b = PQᵀ`, `P, Q` orthogonal),
  `ray_mem` (the ray state is in `𝓜` and `|⟨χ, Z⟩|² = (re² + 3 im²)/6`).
- `GOGlue/Cons.lean`: `CSpec` (the tags of the 64 constraints), `CSpec.mat`, `CSpec.psd` (each constraint matrix is PSD at a point with
  `SliceConstraints`), `RayOK` (rational side conditions of a ray).
- `GOGlue/Orbit.lean`: `orbit_coord` (every `χ ∈ 𝓜` has coordinates `e P diag(η₀) Qᵀ`, `P, Q` orthogonal of either determinant),
  `frame_orth` (a closest-point frame at `v` gives one at `v'` when `sX v' = R sX v Rᵀ`, `sY v' = R sY v Rᵀ`, `R = diag(1, O)`).
- `GOGlue/OrbitMaps.lean`: the 6 permutations and 8 sign changes of the certificate as such conjugations (`frame_perm`, `frame_flip`,
  `frame_orbit`).
- `GOGlue/FrameCert.lean`: `GOFrameCertificate` (`∀ v h, IsFrame (sState v) h → 0 ≤ sliceTarget v`; the certificate only needs the
  constraints at closest-point frames, so no closure of `SliceConstraints` under the group is needed), `GOSliceCertificate.frame`,
  `globalOverlap_of_frame_cert`.

*Data-dependent modules (NOT in the aggregate; they import `GOData/*`, which is generated and not committed):*
- `GOProbe/Check.lean`: the certificate: `check_all` (`native_decide`), `go_target_nonneg`.
- `GOGlue/DataCheck.lean`: `identCheck_true` (`native_decide`: the generated `lit` equals `(mapDen·grid)(sliceTarget − R_sq − R_ax)`
  as sorted sparse polynomials), `lit_ev`.
- `GOGlue/ConsCheck.lean`: `consCheck_true` (`native_decide`: each generated `cons[c]` is a positive multiple of the slice-side matrix
  `consSpec[c]` of `GOData/GOSpec.lean`, and the side conditions of the rays/lower frames), `cons_psd`.
- `GOGlue/Final.lean`: `go_frame_certificate : GOFrameCertificate`; **`globalOverlap_all : ∀ ψ, normSqPsi ψ = 1 → GlobalOverlap ψ`**;
  the unconditional downstream estimates `orbitDist_sq_le_Q_all`, `entropy_gap_orbit_stability_dist_all`,
  `orbitDist_sq_le_Q_tau_all`, `entropy_gap_dist_tau_all`, `majorant_gap_orbit_all`, `tsallis_gap_orbit_all`, and `critical_orbit_sharp_dist_all` (`thm:fqe-critical-orbit-sharp` with no hypothesis).
  Axioms: `propext`, `Classical.choice`, `Quot.sound` and `Lean.ofReduceBool` (the three data checks `check_all`, `identCheck_true`,
  `consCheck_true`, each a decidable check of the generated data by ordinary computable list functions).

*Commands* (from the checkout root; `QIPROJECTS` names the QIprojects checkout, `sympy` is needed):
```
lake build FormalResearch                                   # aggregate; needs no generated data
QIPROJECTS=/path/to/QIprojects python3 FormalResearch/FourQubitEntropy/gen_go_cert.py   # writes the gitignored GOData/
lake build FormalResearch.FourQubitEntropy.GOGlue.Final     # data check + final theorem (about 8.5 min wall, 7.6 GB RSS dominated by the memory-mapped Mathlib, 4 cores shared; the three `native_decide` checks take about 6 min of it)
```

### `thm:fqe-sharp-quadratic-variance` (QV) and its corollaries, unconditionally

The certificate identity `eq:fqe-qv-allstate-sos`, `2D·𝔇(z) = Σ_{k,i} q_ki ‖Φ_ki(z)‖²_w` (14 blocks, 95 covariant norms, data
generated from QIprojects `quadratic_purity_variance_certificate.json` by `QVCert/gen_qv_data.py`), proved for every `z` without
the paper's dimension count. Layers (module docstrings in `QVCheck/All.lean` describe the architecture):
- `QVCert/*`: data, weights and positivity, the covariants `Φ_ki`, the homogenised defect `defectD`, and
  `sharpQV_of_certIdentity : QVCertIdentity → SharpQuadraticVarianceBound`.
- `QVFrame/*`: both sides as a sesquilinear form `conj(z^{⊗6})ᵀ K z^{⊗6}` (J-twisted partial transpose, 37 copy-permutation terms for `𝔇`),
  `cert_diff_eq_qf`.
- `QVBlock/*`: generic block calculus: `quad_eq_zero_of_int_certificate` (per-qubit block diagonalisation by an integer intertwiner,
  certified invariant bases, sector identities `Wᵀ Y V = 0` ⇒ the form vanishes).
- `QVCheckImpl/*` (Mathlib-free, `precompileModules`): the computable checker `checkAll`; `QVCheck/*`: its soundness, discharging every
  hypothesis of the block calculus from `checkAll … = true` (`kfam_bilinear`).
- `QVCheck/Certify.lean`: `checkAll_true` (`native_decide`; about 14 min of the build).
- `QVCheck/Unconditional.lean`: **`QVCert.qvCertIdentity`**, **`RenyiFull.sharpQuadraticVarianceBound`** (QV),
  `RenyiFull.quadraticVarianceBound` (QK, `thm:fqe-quadratic-variance`, inequality only), `RenyiFull.renyi_envelope_above_one_unconditional`
  (`cor:fqe-renyi-gw`, `q > 1`), `RenyiFull.classicalRelaxation`, `meanRenyi_envelope_unconditional`, `meanRenyi_envelope_eq_hs_unconditional`,
  `relaxTriple_of_state_unconditional`, `joint_purity_unconditional` (`thm:fqe-joint-purity`).
  Axioms (guarded by `#guard_msgs`): `propext`, `Classical.choice`, `Quot.sound` and the `native_decide` axioms of `checkAll_true` and of
  one table fact `cArr_rowC` (the checker's intertwiner table is `opaque`).

### Equality statements of (QV) and (QK) (`QVEquality*.lean`, namespace `QVEquality`)
- `thm:fqe-sharp-quadratic-variance`, equality: `quadFam_qv_equality` (equality along the cluster-to-Bell family; `quadFam_purity_eq`,
  `quadFam_F_eq`, `quadFam_VP_eq`: `P = 1 + r²/2`, `F = (1−r²)/2`, `V_P = (1+2r²)²/24`), `quadFam_qv_ratio` (ratio exactly 3),
  `qv_coefficient_optimal`, and `qv_coefficient_iff` (`F² + cP(P−1) ≥ 6V_P` for all unit states iff `3 ≤ c`).
- `thm:fqe-quadratic-variance`, equality: `qk_equality_iff` (from `SharpQuadraticVarianceBound` as hypothesis),
  `qk_equality_classification` / `qk_equality_classification_product` (unconditional: equality iff HS cut spectra, cluster cut
  spectra, or `IsBellProduct ψ`, an LU image of one of the three Bell-pair products; `isBellTriple_iff_bellProduct`), converses
  `hs_triple_eq`, `cluster_triple_eq`, `bell_triple_eq`, and `qk_coefficients_sharp` (9/2 cannot be decreased, 6 cannot be increased).
- `prop:fqe-critical-variance` (RF): `critical_rf` (`P = 1` ⇒ `F ≥ (3/2)s² − s³`, `s⁴ = 24V_P`), its equality case
  `critical_rf_equality_iff` (`0 < s < 1`), `critical_rf_equality_zero` / `_one` (HS / cluster spectra), attainment
  `critical_rf_attained`, and `critical_F_ge_12V`. Proved from the critical normal form via the self-dual/anti-self-dual parts of
  `a ∧ b`, not the paper's Bloch correlation matrix.
  Axioms: the standard three, plus the two QV `native_decide` axioms for the theorems that use (QV) (`QVEqualityMain.lean`, guarded).

### Further Paper E statements (`PaperEGap*.lean`; standard axioms, no `native_decide`)
- `lem:fqe-hs-fidelity-floor` attained at GHZ: `OD.fidelity_floor_ghz_attained` (`Φ = 1/3 = (1+√τ)/6`).
- `prop:fqe-two-flat-rigidity`, the (QF) identification: `PaperECritical.two_flat_QF` (a unit state with two cuts of purity 1/4 is LU-equivalent
  to `quadFam x y`, after the qubit exchange moving the third cut to `12|34`), with `two_flat_renyi` (its Rényi and von Neumann values,
  at most 5/3) and the converse `quadFam_two_flat`.
- `eq:fqe-null-critical-sharp` of `thm:fqe-critical-orbit-sharp`: `CO.null_critical_sharp`, `null_critical_distance`,
  `null_critical_sharp_of_purity`, sharp at the cluster state (`null_critical_attained`); no use of `thm:fqe-global-overlap`.
- Not formalised: the local-radius clauses of `thm:fqe-orbit-stability`; the full list of unformalised Paper E results is in
  QIprojects `docs/lean_status.md`.

### Even-`n` purity–spin-flip tradeoff (`SpinFlipTradeoffEven*.lean`, namespace `PurityLP`; standard axioms, no `native_decide`)
- `thm:purity-spinflip-tradeoff` (`seven_qubit_entanglement/spinflip_tradeoff.tex`) for `n ∈ {8,10,14,16,20}`:
  `purity_spinflip_tradeoff_even` (`π_{n/2} ≥ L_n + c_n τ_n`; dual certificates ST-2–ST-6 checked by `decide +kernel` in
  `SpinFlipTradeoffEvenCert.lean` through `lp_tradeoff`), sharpness `purity_spinflip_tradeoff_even_sharp` (one all-odd-degree graph
  state per `n`, `tau_gsn_eq_one`, kernel-checked `meanRdmPurity_graphT<n>`), `purity_spinflip_tradeoff_even_coeff_optimal`,
  `cor:spinflip-rigidity` as `purity_spinflip_tradeoff_even_stability` / `_minimiser`, and `tau_eq_normSq_bilinear`
  (`τ_n = |ψᵀσ_y^{⊗n}ψ|²`). The entry `n = 4` is `SpinFlip.tradeoff_four_ge`. Generator `gen_spinflip_tradeoff_even.py`;
  The rank sums of the circulant witnesses `n = 16, 20` (and `PurityLPGraphData17`, `n = 17`) are evaluated over one representative of each orbit of the dihedral
  automorphism group (`NQubit/Graph/Symmetry.lean`, `PurityLPSymmetry.lean`: `sum_cuts_reps`), so `SpinFlipTradeoffEvenGraph20.lean` builds in about 5 min.

### Seven-qubit five-copy layers (data-free)
- `SevenFiveCopyDual.lean`: `sevenPurityBound_of_dual` (a five-copy dual identity with PSD weights gives `SevenQubitConseq.SevenPurityBound`,
  `cor:seven-global-from-fivecopy`), `purity_gap_ge_of_dual`.
- `SevenFiveCopyTangent.lean`: `lem:fivecopy-tangent-line` in abstract form (`tangent_line`, `tangent_line_normalised`; equality assertion `tangent_line_eq`), and `equality_moment`, `equality_moment_centred` (the tangent-line step of `thm:fivecopy-family-equality` with the invariant-square argument).
  The certificate FP5-1 itself is not formalised.
