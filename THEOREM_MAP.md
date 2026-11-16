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
| 6j sum first-argument recurrence | `Rec6jSum.racahSum6_recurrence` | key identity `Rec6jKey.rec6_key` (symmetric-variable polynomial certificate; earlier slow-build timing is obsolete) |
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

Not formalised: DLMF 34.5.3, and the bridge theorem is proved in the Physlib fork `cmbant/physlib` (branches `racah/01…24`, not upstream) and mirrored here under `ThirdParty/physlib-racah/` (`NOTICE.md`; the Mathlib-only Saalschütz/Sears files build as `lake build PhyslibRacahHyp`, the rest via `check.sh` in a Physlib checkout): `sixJ_eq_ite_racah6j`, Racah's closed formula for Physlib's operator-defined `sixJ` for all labels (`sixJ = racah6j …` when `ValidA ∧ ValidB`, `0` otherwise, the latter being the definition of `sixJ`), from `sixJ_eq_racah6j` (`0 < a`, `0 < c`; via `sixJ = Cconst · Xs`, a balanced terminating `₄F₃`, and one Sears transformation) and the direct edge cases `a = 0`, `c = 0` (`sixJ_eq_racah6j_zero_left`, `sixJ_eq_racah6j_zero_right`), axioms `[propext, Classical.choice, Quot.sound]`, compiled on Lean 4.35 / Mathlib `56a0058`. `racah6j` itself is not claimed to vanish on inadmissible labels. Not covered: the operator-side three-term recurrence (an earlier prototype had `casMat_eq` as `sorry`; it is not part of the stack). Certificate search scripts: `scripts/wigner_certificates/` (provenance only).

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
| rank ladders (tagged `eq:dranklower`, `eq:drankupper` in the sources; standard identities, no longer displayed equations of the current P2 paper) and the rank recurrence (`eq:3jrank` at `t = 0`, `eq:drank`, Varshalovich 4.8.1) | `wignerSmallD_rank_lower`, `wignerSmallD_rank_upper`, `wignerSmallD_rank_rec`, `wignerSmallDx_rank_lower`, `wignerSmallDx_rank_upper` | `WignerDLadder` | all rational `f m' m`, no admissibility hypothesis (`R_f = 0` exactly where the neighbouring rank is undefined) |
| Jacobi contiguous relations (Szegő §4.5, DLMF §18.9(iii)) | `jacobi_ladder_lower`, `jacobi_ladder_upper` | `WignerDLadder` | `α+β+1 > 0`; from the coefficient recurrence and `jacobi_three_term` |

### Weyl P2: exact finite 6j/Racah statements (`FormalResearch/Racah/P2Racah*.lean`, namespace `Racah.SixJ`)

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex` (as restructured on 2026-11-15/16: titles shortened, unified local calculus in `app:3j-allorder`; labels below are the current ones). This section is the exact finite algebraic part; the analytic half (Λ-expansions, `thm:6jeven`, Wigner `d`,
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
| `prop:unique` (exact algebraic core; the paper's statement is relative to the admitted `f`-independent gauge class) | `unique_affine_core`, `driftX1_eq_zero_iff`, `prop_unique_algebra` | `P2RacahUnique` | expansion half of the proposition not formalised (the expansion theorem it would use is `thm_6jeven`, below) |
| physical `c`- and `f`-lattices are `{c_min..c_max}`, `{f_min..f_max}` (iff statements under `RacahLabels`: `2a, 2b, 2m, m-n ∈ ℤ`), equal cardinality `eq:Racahdimension` | `physC`, `physF`, `mem_physC_iff`, `mem_physF_iff`, `ncard_physC_eq_ncard_physF` | `P2RacahSystemLattice` | |
| `eq:RacahHamiltonian` as a concrete matrix; self-adjointness in the weight `ω_c` | `HR`, `wgtR`, `HR_selfadjoint_entries`, `HR_selfadjoint`, `HRsym_isHermitian` | `P2RacahSystemOp` | |
| `eq:RacahPhiOrthogonality` (from 34.5.14) | `sixJ_orth_physical`, `weight_Phi_mul`, `Phi6_orthogonality` | `P2RacahSystemOrth` | |
| orthonormal eigenbasis `v_f`, `eq:RacahPhiCompleteness`, spectrum `{f(f+1)}`, simplicity, characteristic polynomial | `vR_eigen`, `vR_orthonormal`, `Phi6_completeness`, `vR_expansion`, `HR_spectrum`, `HR_eigenspace`, `HR_charpoly` | `P2RacahSystemSpec` | completeness by the dimension identity (square matrix with orthonormal rows) |
| **`thm:6jfiniteRacah`** (exact finite self-adjoint Racah–Wigner system) | `thm_6jfiniteRacah` (hypothesis `RacahSystem a b m n D`, satisfiable iff the lattice is non-empty) | `P2RacahSystem` | conjunction of the lattice, detailed-balance, eigen, orthonormality, completeness, spectrum, simplicity and charpoly statements |
| the paper's non-emptiness hypothesis for `thm:6jfiniteRacah` ("with `b+m, a+n ≥ 0` and `f_1 ≥ f_0`, so that the lattices are non-empty", opening of `sec:6jcspectral`) | `racah_nonempty_tfae`, `nonneg_of_fMin_le_fMax`, `racah_empty_example` | `P2RacahNonempty` | under `RacahLabels`: `physC` non-empty ⇔ `physF` non-empty ⇔ `c_min ≤ c_max` ⇔ `f_0 ≤ f_1` ⇔ (`b+m, a+n ≥ 0` and `f_0 ≤ f_1`) ⇔ `∃ D, RacahSystem a b m n D`; the two conditions `b+m, a+n ≥ 0` are consequences of `f_0 ≤ f_1`. So `thm_6jfiniteRacah` is exactly the paper's theorem under its stated hypothesis |
| Racah-to-Wigner spectral map (`prop:6jRacahTransmutation`, a corollary in the current paper) | `SRmap`, `SRmap_u`, `SRmap_isometry`, `SRmap_SRinv`, `SRinv_SRmap`, `SRmap_intertwine` | `P2RacahSystemWigner` | **abstract form**: orthonormal family in a real inner-product space. The realisation in `L²(-1,1)` with Wigner `d`-functions and the kernel `eq:6jRacahKernel` is `prop_6jRacahTransmutation`, `SR_kernel`, `SR_intertwine_diff` (`P2AnalyticL2Transmutation`) |
| **Racah-polynomial realization** (`eq:physicalRacah4F3`, `eq:physicalRacahParameters`): `Φ_{m+r}(c_min+y)/Φ_m(c_min+y)` is the terminating `₄F₃(-r, r+2m+1, -y, y+2c_min+1; m-n+1, m+n+c_min+c_max+2, -D; 1)` (the paper's ratio `𝒰_r` of `eq:physicalRacahPolynomial` is `physR`, written `ℛ_r` in the docstrings) | `ppR_eq_racahPoly`, `physQ`, `racahPoly`, `racahPoly_diff` | `P2RacahPolyIdent`, `P2RacahPolyDiff` | proved by uniqueness of the solution of the three-term difference equation (6j side: `ppR_row`; polynomial side: `racahPoly_diff`), not by a rearrangement of sums |
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
| `prop:HahnJacobi` (appendix `app:beta-polar`; exact finite Hahn algebra: `[C,X] = 2(X²-1)+4h²(H-(Σ-1)/2)`, `[H,C] = 2{H,X}-4Mσ`) | `Cop`, `finiteHahn1`, `finiteHahn2`, `finiteHahn2_lattice` | `P2HahnAlgebra` | the second relation needs the edge conditions on `x` (or the four `IsNat` conditions) |
| `lem:polarintertwiner` (appendix `app:beta-polar`; polar unitary of a finite intertwiner, finite-dimensional complex Hilbert spaces) | `gram_commute`, `polarU_unitary`, `polarU_intertwines` | `P2HahnPolar` | over `ℂ` (Mathlib functional calculus); the real case follows by complexification |
| beta–binomial realization (appendices `app:beta-polar`, `app:beta-polar-sv`; classical structure the main results do not use), finite part: Bernstein–Hahn–Jacobi identity `eq:BernsteinHahnJacobi` (Jacobi side as the terminating `₂F₁`), singular values `eq:singularvaluesgeneral`, `eq:physicalsingularvalues` | `bernstein_moment`, `bernstein_hahn_jacobi`, `singularSq`, `singularSq_pos`, `singularSq_physical` | `P2HahnBeta` | `prop:SN` is `prop_SN` (`P2AnalyticL2Transmutation`) and the singular-pair relation is `singular_pair` (`P2AnalyticL2Singular`); the Jacobi side is identified with `jacobi` by `hypergeometric_eq_jacobi` |
| `eq:3jdiscorth`, `eq:3jdisccomplete` (hypothesis `SpecAdm M σ N` encodes the paper's integrality assumptions) | `Phi_discorth`, `Phi_disccomplete` | `P2ThreeJSystem` | from 34.3.17 / 34.3.16 |
| spectrum of `𝖧_h` is `{L(L+1)}`, simple; eigenvectors multiples of `Φ_L` (`thm:3jspectral`, the finite part) | `Hh_spectrum_iff`, `Phi_latEigen`, `rankEig_strictMono`, `Hh_eigen_simple` | `P2ThreeJSystemSpec` | symmetry from `Hh_lattice_symmetric` |



### Weyl P2: analytic half (`FormalResearch/Racah/P2Analytic*.lean`)

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`. Merged to `master` from branch `wigner-3j6j` (PR #81). All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`).
Conventions: `Phi3j L M σ N μ` at `x = 2μ/N`, `t = h² = N⁻²`; `Phi6 … f m n` at `A = wA a n`, `B = wB b m`, `C = wC c`, `S = A+B+C` (the paper's `Λ`); the paper's `d^L_{Mσ}(arccos x)` is
`wignerSmallDx L M σ x`; `Lat4`/`SpecAdm` (3j) and the four integrality facts `f ± m`, `f ± n ∈ ℕ` (6j) encode the physical lattice.

| paper statement | Lean | file | note |
|---|---|---|---|
| `lem:centeredshift` (central products `𝔠_r(u,h)` as `Ct r u t`, `t = h²`; analyticity, positivity, log estimate, `Γ`-ratio form); uniform Taylor remainder of a jointly smooth `G(z,t)` in `t` | `Ct`, `Cprod_eq_Ct`, `Ct_zero_t`, `analyticAt_Ct`, `Ct_pos`, `abs_log_Ct_sub_le`, `Ct_Gamma`; `taylor_mean_remainder_bound`, `taylorCoeff` | `P2AnalyticCt`, `P2AnalyticCore`, `P2AnalyticTaylor` | generic analytic input of every expansion below; scalar analytic propagation `analyticAt_recurrence_two`, central-binomial convolution `sum_centralBinom_mul` |
| **`lem:sqrtfreecarrier`**, 3j (`eq:sqrtfreecarrier`, `eq:3jrankpoly`, `eq:3jcarrierstart`; `sec:3jcarrier`; all four chambers, all ranks `L ≤ N-1`) | `ptilde3`, `ptilde3Poly`, `Phi3j_carrier`, `Phi3j_eq_Gc3`, `ptilde3_rank_poly`, `natDegree_ptilde3Poly_le`, `dZero3_rank_rec` | `P2AnalyticCarrier3j{,Def,Seed,Rec}` | closed-form germ `Gc3 M σ k x t`; polynomial in `τ` (the paper's `ς = (1-x)/2`) of degree `≤ k`, constant leading coefficient `lead3`. The identification `P̃_L = k_{3j} q_{L-L_0}` with the even Hahn deformation (`eq:carrierHahnRacah`, `lem:evendeformation`) is `ptilde3_eq_hahn`, `lem_evendeformation3` (`P2AnalyticCarrierHahn`, row below); Lean defines `P̃` by the recurrence and identifies its `t = 0` value with the Wigner `d` (`dZero3_eq_wignerD`) |
| **`lem:sqrtfreecarrier6j`** (the 6j half, a separate lemma in the current paper; `eq:sqrtfreecarrier6j`, `eq:6jrankpoly`, `eq:6jEdgeProducts`, `lem:6jseed`, `eq:6jexceptionalseed`; all chambers, sign `ε_{mn} = ε(n,m)`) | `ptilde6`, `ptPoly`, `piSix`, `Phi6_seed_carrier`, `Phi6_carrier_canonical`, `Phi6_carrier_all`, `edgeSq_eq_EW_sq`, `ptilde6_symm_uv` | `P2AnalyticCarrier6j{,Induction,Chambers,Shape,Poly}` | germ `G6 f m n α β γ t`. The sign is `chamberSign = signE3 n m` (`chamberSign_eq_signE3`): `(-1)^{m-n}` for `m ≤ n`, `1` for `m > n`. `P̃_f` symmetric under `A ↔ B` (`ptilde6_symm_uv`; for the germ and `G_{f,2r}`: `G6c_swap`, `G6_swap`, `G6even_swap`, `P2AnalyticSymm6j`). The identification `P̃_f = k_{6j} q_{f-m}(ς; S⁻¹, δ)` (`eq:carrierRacah6j`, `lem:evendeformation6j`) is `ptilde6_eq_racah`, `lem_evendeformation6` (`P2AnalyticCarrierRacah`, row below), canonical sector |
| **`eq:carrierHahnRacah`**, **`lem:evendeformation`** (3j, every chamber, Lean form): `P̃_{L₀+k}(ς; N⁻²) = c · Q_k(Nς-(α+1)/2; α,β,D)`; the even Hahn deformation `q_d = P̃/k_{3j}` is monic of degree `d` with coefficients polynomial in `h²`, equals the monic Jacobi `P̂_d` at `t = 0` and is a nonzero multiple of the Hahn polynomial at every admissible `N`, `d ≤ D = N-L₀-1` | `hahnPoly`, `eval_hahnPoly`, `ptilde3_lattice_hahn`, `ptilde3_eq_hahn`, `evenHahn3`, `lem_evendeformation3`; `evenHahn3_bound`, `evenHahn3_one_const` | `P2AnalyticCarrierHahn`, `P2AnalyticEvenDegree3` | **different order from the paper**: Lean defines `P̃` by the recurrence `eq:3jrankpoly` (polynomial in `h²` immediate), proves the lattice proportionality from `Phi3j_carrier` and `Phi3j_hahn_all_chambers` (the common edge factor cancels against the `n = 0` row) and lifts it to polynomials in `ς` by `D+1 > k` points; evenness of the Hahn deformation is then a corollary, so the difference-equation computation of the paper's proof of `lem:evendeformation` is not used. The estimate `sup_{0≤ς≤1}|q_d - P̂_d| ≤ C N⁻²` is `evenHahn3_bound` (`P2AnalyticEvenDegree3`, `|q_d(ς;t) - P̂_d(ς)| ≤ C t`, `0 ≤ t ≤ 1`, `0 ≤ ς ≤ 1`); `evenHahn3_one_const`: for `d = 1` the Hahn zero does not move (`q_1` is independent of `t`) |
| **`eq:carrierRacah6j`**, **`lem:evendeformation6j`** (6j, every chamber, Lean form; the paper states both in the canonical chamber `m ≥ |n|`, with `P̃_f` "the polynomial of the canonically reduced family" elsewhere): `P̃_{m+r}(ς; A⁻²,B⁻²,(AB)⁻¹) = c · R_r(λ(ς))`, `λ(ς) = 4ABς + (A-B)² - (c_min+½)²`, `R_r` the terminating Racah polynomial of `eq:physicalRacah4F3`; the even deformation `q_d = P̃/k_{6j}` is monic of degree `d`, polynomial in `(A⁻²,B⁻²,(AB)⁻¹)`, equals the monic Jacobi `P̂_d^{(|m-n|,|m+n|)}` at zero scale and is a nonzero multiple of the Racah polynomial of the reduced system on every `RacahSystem`, `d ≤ D`; **all chambers**: the four chambers reduce to the canonical one by the two `6j` symmetries, which preserve `c_min, c_max, D` and the integrality (`racahSystem_chamber`), and the signed carrier polynomial is `k_{6j} q_d` with `k_{6j} = kLeadAll = ε(n,m)κ_d(|m-n|,|m+n|)` (`carrierPolyAll_eq_kLeadAll_mul_evenRacah6`), so that `Φ_f = E W Π_f^{-1/2} k_{6j} q_d(ς; A'⁻², B'⁻², (A'B')⁻¹)` at every physical point (`Phi6_eq_kLeadAll_mul_evenRacah6`, the sign inside `k_{6j}`); **degree bound**: every monomial `τ^i s₁^a s₂^b w^c` of `P̃_{m+d}` (`s₁ = u+v`, `s₂ = uv`, `w`) has `i + 2a + 2b + c ≤ d` (`ptPoly_inFil`), whence the coefficient of `ς^{d-j}` of `q_d` is `∑_{s ≤ j} ε^{2s} M_s(δ²)/(1-δ²)^j` with `M_s ∈ ℝ[X]` (`evenRacah6All_coeff_form`, `coeff_form`); **`eq:evendeformationbound`** (`evenRacah6All_bound`: `|q_d(ς;ε,δ) - P̂_d(ς)| ≤ C ε²` for `0 < ε ≤ 1`, `|δ| ≤ δ₀ < 1`, `0 ≤ ς ≤ 1`; `shapeEval_eq_AB` relates `q_d(ς;ε,δ)` to `(A,B)`) | `racahLam`, `eval_racahLam`, `ptilde6_lattice_racah`, `ptilde6_eq_racah`, `evenRacah6`, `lem_evendeformation6` (canonical); `racahSystem_chamber`, `evenRacah6All`, `carrierPolyAll_eq_kLeadAll_mul_evenRacah6`, `lem_evendeformation6_all`, `Phi6_eq_kLeadAll_mul_evenRacah6` (`P2AnalyticCarrierRacahAll`); `FilS`, `InFil`, `ptPoly_inFil`, `coeff_form`, `evenRacah6All_coeff_form`, `shapeEval`, `shapeEval_eq_AB`, `evenRacah6All_bound` (`P2AnalyticEvenDegree6`) | `P2AnalyticCarrierRacah`, `P2AnalyticCarrierRacahAll`, `P2AnalyticEvenDegree6` | same reversed route as the 3j row (lattice proportionality from `Phi6_carrier_canonical`, `Phi6_seed_carrier`, `ppR_eq_racahPoly`; edge factor cancels; lifted to polynomials in `ς` through `λ = y(y+2c_min+1)`); the degree bound is proved from the carrier recurrence `eq:6jrankpoly` by a weight filtration, not from the Racah difference operator `ℒ_ε` of the paper's proof (the diagonal coefficient has weight 1, the backward coefficient `η_f²` weight 2, and `P̃_{f+1}` is built from `P̃_f` and `P̃_{f-1}`), and `eq:evendeformationbound` is stated for `ε ≤ 1` (the paper leaves the range of `ε` implicit); in chambers III, IV the reduced edges are `(B,A)`, immaterial since `P̃` is symmetric in `A ↔ B` (`ptilde6_symm_uv`) |
| **`sec:6jFludedefect`**, `eq:Fludedefect` (with `eq:Fludenorm`, `eq:Fludeangle`, `eq:deltaF`) | `Psi6`, `xFlude`, `Psi6_eq_mul_Phi6`, `sec_6jFludedefect`, `flude_core`, `cosA_shift_identity`, `taylor_two_uniform`, `analyticOnNhd_wignerSmallDx_hlab` | `P2AnalyticFludeDefect` | `Ψ_f - d(x_F) = Λ⁻¹[r_F d(x) - δ_F d'(x)] + O(H⁻²)` uniformly on `𝒯_δ` (`Λ = A+B+C`, `α = A/Λ`, `β = B/Λ`), from `thm_6jeven` at `R = 1`, the exact `Ψ = √((2A+f)(2B+f))/(2√(AB)) Φ`, an exact identity for `x_F - x` and a uniform second-order Taylor bound of `d`; the genericity (`r_F d - δ_F d' ≠ 0`) is not formalised |
| `t = 0` carrier is Wigner `d` (`G(x,0) = d^L_{Mσ}(arccos x)`, 3j; `G_{f,0} = d^f_{nm}(arccos x)`, 6j including the transposition phase `(-1)^{m-n}` of chambers II/III) | `dZero3_eq_wignerD`, `Gc3_zero_eq_wignerD`; `dZero6c_eq_wignerD`, `dZero6_eq_wignerD`, `G6_zero_eq_wignerD` | `P2AnalyticBridge3j`, `P2AnalyticBridge6j` | induction in the rank against `wignerSmallDx_rank_rec` |
| `eq:WignerJacobiMonic`, `eq:WignerJacobiMonic6j` (`d = k W P̂^{(p₊,p₋)}`, `k_{3j} = lead3`, `k_{6j} = ε(n,m) κ = kLead` in the canonical chamber) | `lead3_eq_jacobi`, `lead3_eq_closed`, `wignerD3_eq_lead_mul_monic`; `kLead_eq_jacobi`, `kLead_eq_closed`, `wignerD6_eq_kLead_mul_monic` | `P2AnalyticLeading` | constants identified by comparing top coefficients; 3j all chambers; 6j Wigner form in the canonical chamber (`m ∓ n` natural); 6j carrier-polynomial leading coefficient `ε(n,m)·κ_d(|m-n|,|m+n|) ≠ 0` in all four chambers (the paper's `ε_{mn} = ε(n,m)`, so `P̃_f` itself has leading coefficient `κ_d`, and the signed `ε P̃_f` has `k_{6j}`): `kLeadAll_eq_signE3_mul_kappa`, `kLeadAll_ne_zero`, `carrierPolyAll_natDegree`, `Phi6_eq_poly_all` (`P2AnalyticLeading6jChambers`); all-chamber Wigner form `d^f_{nm}(arccos x) = k_{6j} W_{6j} P̂_d^{(|m-n|,|m+n|)}`, `k_{6j} = kLeadAll`, `d = f - max(|m|,|n|)`: `wignerD6_eq_kLeadAll_mul_monic`, `wignerD6_eq_signE3_mul_kappa` (`P2AnalyticWignerJacobi6j`, from `dZero6_eq_wignerD`) |
| **`thm:3jeven`** (`eq:3jevenexp`): analytic germ `G` on `U × (-ρ,ρ)`, `Φ = G(x,N⁻²)`, `f_0 = d`, expansion in `N⁻²` to every order with remainder `O_K(N^{-2R})`, `f_{2r}` analytic on `(-1,1)` | `thm_3jeven`, `thm_3jeven_noOdd`, `thm_3jeven_leading`, `Phi3j_even_expansion`, `Gc3_analytic_box`, `analyticOnNhd_f3even`, `analyticOnNhd_wignerSmallDx_of_labels` | `P2AnalyticHeadline`, `P2AnalyticBulk3j` | |
| `cor:3jcoeffsym` (`eq:coeffRegge`, `eq:coeffSign`, `eq:coeffTranspose`), `rem:spinhalf`, `rem:movingpoint` | `f3even_regge`, `f3even_negMσ`, `f3even_swap`; `Phi3j_half_exact`, `Phi3j_half_expansion`; `Phi3j_moving_point`, `rem_movingpoint` | `P2AnalyticBulk3j`, `P2AnalyticHeadline` | coefficientwise from the exact symmetries of `Gc3` |
| **`thm:6jeven`** (`eq:6jleading`, `eq:6jevenexp`): `G_{f,2r}` analytic and homogeneous of degree `-2r` on the strict-triangle cone (also symmetric under `A ↔ B`, `G6even_swap`), `G_{f,0} = d^f_{nm}(arccos x)`, germ in `Λ⁻²` (Lean `S⁻²`) with uniform radius over compact shape sets, `Φ_f = ∑_{r<R} G_{f,2r} + O(H^{-2R})` on `T_δ` | `thm_6jeven`, `Phi6_even_expansion`, `Phi6_even_expansion_cone`, `G6even`, `G6even_homogeneous`, `analyticOnNhd_G6even`, `Phi6_eq_G6` | `P2AnalyticHeadline6j`, `P2AnalyticBulk6j` | holomorphy paragraph of `lem:6jseed` in its real-analytic form (`analyticAt_ptilde6`); `StrictTri`, `TriDelta` |
| **`thm:uniformedge`** (a) (`eq:3juniformedge`) and (b) (`eq:6juniformedge`), `W s_0 = d`; edge-factor bounds `0 < c ≤ E ≤ 1` and `eq:edgefactoroverlap`, `eq:universalEdgeFactor` | `thm_uniformedge_3j`, `Phi3j_uniform_edge`, `edgeS3`, `natDegree_edgeS3_le`; `thm_uniformedge_6j`, `Phi6_uniform_edge`, `Phi6_edge_factor`, `edgeE_bounds`, `edgeR_pos_le_one`, `edgeR_expansion`, `analyticOnNhd_cKc` | `P2AnalyticHeadline`, `P2AnalyticHeadline6j`, `P2AnalyticUniform3j`, `P2AnalyticUniform6j` | uniform on the whole physical lattice under `λ ≤ A/B ≤ λ⁻¹` (6j, `eq:6jedgeratiobound`); the 6j coefficients `s_r` are analytic and even in `δ ∈ (-1,1)` (`s6_neg_delta`; rationality in `δ` with poles at `±1`, and the last sentence of the theorem on the convergence domains `N > L`, `2 min(A,B) > f` with their exactness, not formalised); `0 < c ≤ E ≤ 1` is for the 6j edge factor (the 3j edge-factor bounds alone are not stated) |
| **`thm:3jNLO`** (`eq:3jimproved`, `eq:3jf2`, `eq:3jf2seednorm`), Gaunt remark to `N⁻²` | `f3even_one_eq_nloF2`, `Phi3j_nlo_expansion`, `Phi3j_gaunt_nlo`, `nloH_rec`, `nlo_seed_alg`, `nlo_e_eq`, `qt3_rank`, `f3even_one_eq` | `P2AnalyticNLO3j{,Alg,Deriv}` | remainder `C N⁻⁴`; inhomogeneous rank recurrence for `f_2 - (2L+1)L(L+1)d_L/12` from the ladders differentiated once and the ODE. The Gaunt `N⁻⁴` coefficient `J(5J-4)/32` needs `thm:3jNNLO` and is not formalised |
| **`cor:uniformNLO`**, 3j half (`eq:3juniformNLO`) | `Phi3j_uniform_nlo` | `P2AnalyticNLO3jUniform` | the paper's `e_2^{3j}(x)` is `N`-free and the statement reads `E_N[d + N⁻²(f_2 - e_2^{3j} d)]`; Lean's `e2three M σ N x = N⁻² e_2^{3j}(x)`, same statement. Explicit polynomial form of `f_2 - e_2^{3j} d` (with cancelling endpoint poles) not formalised |
| **`cor:uniformNLO`**, 6j half (`eq:6juniformNLO`) | `Phi6_uniform_nlo`, `edgeW_mul_s6_one`, `G6closed_sub_e2_eq_poly` | `P2AnalyticNLO6jUniform` | proved under the ratio bound `λ ≤ A/B ≤ λ⁻¹` of `eq:6jedgeratiobound`, explicitly included in the paper's corollary and used for the `O((A+B)⁻⁴)` remainder; `W ×` polynomial form of `G_{f,2} - e_2^{6j} d` proved |
| **`thm:6jclosedcorrection`** (`eq:6jclosedg`, `eq:6jPf`, `eq:6jQf`, `eq:6jG2operator`, `eq:kappaClosedMatch`), all four chambers | `a6_one_closed`, `G6even_one_eq_closed`, `Phi6_nlo_expansion`, `Phi6_nlo_expansion_cone`, `nlo6_e_eq`, `nlo6H_rec`, `nlo6_seed_alg`, `nlo6P`, `nlo6Q` | `P2AnalyticNLO6j{,Alg,Deriv}` | remainder `C S⁻⁴` on compact shape sets, `C H⁻⁴` on `T_δ`; no `6j` degree `-4` term. **Different route from the paper**: the paper derives `eq:6jclosedg` from the general local calculus (`prop:localcalculus`, with the master commutator `eq:3jmastercommutator`, `eq:3jJoperator`, instance `eq:generalrankrec`, then fixes the scalar multiplier at the seed by `eq:kappaClosedMatch`); the exact algebra of that calculus is formalised abstractly in `P2LocalCalculus` (row *Weyl P2: local calculus* below), its instance on the Wigner `d` for the `3j` kernel is formalised (rows below), the `6j` instance and the seed matching `eq:kappaClosedMatch` are not; Lean differentiates the carrier recurrence once in `t` and compares it with the Wigner ladders differentiated once in `x` (one rational identity `nlo6H_rec`), then matches the seed (`nlo6_seed_alg`). The statements agree (same `P_f`, `Q_f`) |
| `eq:continuummass` (`rem:normmatch`): `∫_{-1}^1 d^L_{Mσ} d^{L'}_{Mσ} dx = 2/(2L+1) δ_{LL'}`; Wigner modes `u_L` orthonormal in `L²(-1,1)`; `𝖧₀ u_L = L(L+1) u_L` (`eq:H0`) | `integral_wignerSmallDx_mul`, `integral_wignerSmallDx_sq`, `uWig`, `integral_uWig_mul`, `L2uWig_orthonormal`, `H0diff`, `H0diff_uWig`, `H0diff_sum` | `P2AnalyticL2Wigner` | `L2cont` is the class in `Lp ℝ 2 (volume.restrict (Icc (-1) 1))` |
| **`prop:SN`** (`eq:SNspectral`–`eq:SNintertwine`): `S_N u_L = v_L`, isometry, unitary from `span{u_L}` onto `ℓ²(𝒳_N,2h)`, `𝖧_h S_N = S_N 𝖧₀`; kernel `eq:SNkernel` | `vN_orthonormal`, `vN_expansion`, `SNmap_u`, `SNmap_isometry`, `SNmap_intertwine` (abstract, `P2AnalyticL2ThreeJ`); `uN_orthonormal`, `prop_SN`, `SN_kernel`, `SN_intertwine_diff` | `P2AnalyticL2ThreeJ`, `P2AnalyticL2Transmutation` | `𝒱_N` is the finite span, as in the paper; `S_N` on all of `L²` and `L²` completeness of `{u_L}` not formalised |
| **`prop:6jRacahTransmutation`** (`eq:6jRacahSpectralMap`–`eq:6jRacahIntertwine`), kernel `eq:6jRacahKernel` | `uR_orthonormal`, `prop_6jRacahTransmutation`, `SR_kernel`, `SR_intertwine_diff` | `P2AnalyticL2Transmutation` | exactly parallel to `prop_SN`, under `RacahSystem a b m n D` |
| **`prop:betabinomialpolar`**, singular-pair relation `T_D J_n = s_n H_n` (`eq:singularvaluesgeneral`, `eq:betameasure`–`eq:conditionalC`, `eq:BernsteinAdjoint`) | `singular_pair`, `norm_relation`, `Cop_jT`, `ipP_Cop`, `ipJ_jT_orth`, `hahn_orth`, `hahn_determined`, `pD_eq_hahnW`, `beta01` | `P2AnalyticL2Singular` | Jacobi orthogonality in `L²(ν_H)`, Hahn orthogonality in `ℓ²(p_D)`; polar decomposition, gauges and `eq:SNpolar` are in the next row |
| **`prop:betabinomialpolar`** polar part: `U_D = T_D(T_D^*T_D)^{-1/2}`, `U_D J_n = H_n`, gauges `G_c`, `G_d`, **`eq:SNpolar`** `S_N G_c = G_d U_D`, whitening `eq:SNwhitening`, `eq:physicalsingularvalues` and its Gamma form | `polarFactor`, `polarFactor_basis`, `polarFactor_intertwine` (abstract, `lem:polarintertwiner`); `UD_JV`, `UD_unitary`; `vN_eq_Gd`, `uN_eq_Gc`, `Gc_inner`, `eq_SNpolar`, `eq_SNpolar_inv`, `eq_SNwhitening`, `sing_sq_physical`, `sing_sq_gamma`, `prop_betabinomialpolar` | `P2AnalyticL2PolarAbs`, `P2AnalyticL2Polar`, `Polar2`, `Polar3`, `Polar4` | polar factor via a spectral positive root (no CFC for real Hilbert operators); `ℓ²(p_D)` realised as `ℝ^{D+1}` via `q ↦ √p_D q`; `G_c` defined as the linear extension on the `J_n` basis (the pointwise characterisation for general `φ` is not formalised); whitening stated on the basis, no operator-level `𝖧₀`/`L̂`; the partial-isometry remark for the unrestricted `C_D` not formalised |

Not formalised in the analytic half: `L²` completeness of the Wigner modes; rationality in `δ` of `s_r` and the convergence domains and exact radii (`rem:exactradii`);
`thm:3jNNLO` (with `app:D4`) and the `6j` degree `-4` term, the Gaunt `N⁻⁴` term; rationality of the multipliers of the all-order operators `D̂_{2r}` (`prop:localcalculus`(b) and `thm:3jallorderlocal` are formalised with smooth multipliers, see below), the `6j` instance `thm:6jallorderlocal` (with the `A ↔ B` symmetry of the operators `𝒢_{2r}`; the coefficient-level symmetry of `G_{f,2r}` is `G6even_swap`), the `ℓ²`-sampled form `cor:sampledSN`, `lem:6jseedrational`; the hard-edge corollaries `prop:LaguerreEdge`, `thm:6jhardedge`, `rem:Laguerre`; the genericity of the Edmonds/Flude-variable defect `sec:6jFludedefect` (that it is nonzero; the expansion `eq:Fludedefect` itself is formalised); the expansion halves of `prop:3junique` and `prop:unique`; DLMF 34.5.3; the bridge to Physlib's abstract `sixJ`.

### Weyl P2: local calculus (`FormalResearch/Racah/P2MomentPolynomial.lean`, `P2LocalCalculus*.lean`, `P2AnalyticAllOrder3j*.lean`, `P2AnalyticTaylorSeries.lean`, namespace `Racah.LocalCalculus`)

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, appendix `app:3j-allorder`, subsection `app:localgeneral`. Over a field of characteristic zero; the operators `x, H₀, 𝖠` are arbitrary endomorphisms of a module and `d_{k-1}, d_k, d_{k+1}` arbitrary vectors satisfying the Wigner rank recurrence and `H₀ d_j = λ_j d_j` at one rank `k` (no differential operators needed). All headline theorems depend only on `[propext, Classical.choice, Quot.sound]`. The `3j` instance rows below are the concrete `ℝ`-function module.

| paper statement | Lean | file | note |
|---|---|---|---|
| **`lem:momentpolynomial`** (`eq:3jpimoment`, `π_1 = z`, `π_2 = z(z-1)`) | `momentMap`, `momentMap_bijective_even`, `momentPoly_exists_unique`, `momentPoly`, `momentPoly_spec`, `natDegree_momentPoly`, `monic_momentPoly`, `momentPoly_eval_zero`, `momentPoly_one`, `momentPoly_two` | `P2MomentPolynomial` | stronger than the paper: `T[p](y) = p(y²-y)+p(y²+y)` is a bijection from `K[z]` onto *all* even polynomials, and uniqueness of `π_s` holds among all polynomials (degree `s` and monicity follow) |
| `eq:3jmastercommutator` | `master_commutator` | `P2LocalCalculus` | `ℒ_W(𝖠d)_k = -(2k+1)λ_k[x,𝖠]d_k` from the Wigner recurrence at `k` |
| `eq:3jNsOperator`, `eq:3jneighbormomentidentity` | `Ns`, `neighbor_moment_identity`, `neighbor_moment_identity_of` | `P2LocalCalculus` | for `π_s` of `lem:momentpolynomial`; `_of` for any `π = zπ̃` with the two neighboring-moment relations |
| `prop:localcalculus` (a) (`eq:generalrankrec`, `eq:3jB2r`, `eq:3jD2rrecursive`) | `local_calculus_order` | `P2LocalCalculus` | order-by-order: if `[x, 𝒢_{2r+2}] = 𝖡_{2r+2}` then the order-`2r+2` coefficient of the deformed recurrence vanishes (order `0` is the Wigner recurrence); the formal-series resummation is `local_calculus_series` (`P2LocalCalculusSeries`): for `G 0 = 1` and `[x,G_{r+1}] = 𝖡_{r+1}`, the series `∑ t^r 𝒢_r d_k` satisfies the all-order rank recurrence (`serG`, `eta`, `Bop`, `rankDefect`) |
| `eq:3jJoperator` | `Jop`, `leftNormal`, `commutator_J` | `P2LocalCalculus` | `[x, 𝒥(𝖡)] = 𝖡` in any ring with `[∂, x] = 1` and coefficients commuting with `x` |
| `prop:localcalculus` (c), `eq:3jscalarNsone` | `Ns_apply_one`, `Ns_apply_one_momentPoly`, `scalar_start_recursion` | `P2LocalCalculus` | `𝒩_s[𝖠]1 = 𝖠x` and the recursion `a_{r+1} = -q(0)G_r1 - ∑ e_{s+1}a_{r-s}`; the sum `η(1)∑a_r = x - q(0)` as formal series is `scalar_start_series` (`P2LocalCalculusSeries`); there the vanishing `G_{r+1}·1 = 0` of the start is a hypothesis, derived in the `3j` instance from the vanishing physical coefficients, not from the paper's argument that `𝒥(𝖡)` has only positive derivative orders |
| `prop:localcalculus` (a)+(b)+uniqueness, abstract (`eq:3jD2rrecursive`, `eq:3jpsi2r`) | `prop_localcalculus`, `exists_solution`, `local_calculus_start`, `local_calculus_ranks`, `exists_mult_eq`, `Jsol`, `LN`, `rank_unique_of_start`, `rank_unique_of_two_starts` | `P2LocalCalculusLeftNormal`, `P2LocalCalculusSeries` | left-normal operators `LN D C = span{c ∂^j}` over a multiplier algebra `C` (closed under `c ↦ [∂,c]`); recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` with the multiplier `ψ` fixed by `𝒢_r d₀ = κ_r d₀` (needs `∂ d₀ = w d₀`, `w ∈ C`); the resulting formal solution is rank-defect free and unique among formal series with the same start. The `ψ_r` are only shown to lie in `C` (smooth multipliers in the instance), not rational |
| instance on the Wigner `d` (`eq:H0`, `eq:dODE`) | `Fn`, `xOp`, `DOp`, `Csm`, `Crat`, `Hop`, `Hop_mem_LN_sm`, `Hop_wigF`, `wigF_rank` | `P2LocalCalculusFun`, `P2LocalCalculusWigner` | functions `ℝ → ℝ`, smooth on `(-1,1)`, zero outside; `𝖧₀ d^L_{Mσ} = L(L+1) d^L_{Mσ}` and the Wigner rank recurrence in `Fn` |
| **`thm:3jallorderlocal`** (`eq:3jallorderoperator`), link to the physical kernels (`app:localgeneral`, *Link to the physical kernels*) | `allorder_operators`, `allorder_operators_pos`, `allorder_operators_zero`, `threeJ_allorder_local`, `gTest`; formal side: `Psi_rank`, `Gc3_rankDefect`, `Psi_zero_zero_one`, `taylorSer`, `sqrt1m`, `eta_c3`, `Lk_succ`, `sF_relation` | `P2AnalyticAllOrder3j`, `P2AnalyticAllOrder3jSeries`, `P2AnalyticTaylorSeries` | for `M±σ` integers and all four chambers: rank-independent `𝒢_r ∈ LN ∂ Csm`, `[x,𝒢_{r+1}] = 𝖡_{r+1}` (`eq:3jB2r`, `q = 0`, `e_s` the coefficients of `√(1-z)`), and `f_{2r}^{(n)}(x) = (𝒢_r d_n)(x)` for every rank `n`, order `r`, `x ∈ (-1,1)` (`f3even` is the Taylor coefficient of the exact closed form `thm:3jeven`); `threeJ_allorder_local`: pointwise remainder `C N^{-2R}` for `|S_N g(x_μ) - ∑_{r<R} N^{-2r}(𝒢_r g)(x_μ)|`, `g` in the unit ball of the cutoff space, `2μ/N ∈ K` compact, from `Phi3j_even_expansion`. Differences: the coefficients are smooth on `(-1,1)`, rationality of `ψ_r`/`D̂_{2r}` and the pole statement at `x = ±1` are not formalised, and the statement is pointwise (the `ℓ²(𝒳_N ∩ K)` form of `cor:sampledSN` follows from it by summation, not stated); `D̂_2`, `D̂_4` closed forms (`thm:3jNNLO`, `app:D4`) are not part of it (at the seed row the multipliers are identified with the seed coefficients `κ_r` of `eq:3jseedlogallorder`: see the next row) |
| **`eq:3jseedlogallorder`** (`app:3j-allorder`, *The `3j` instance*): `log(Φ_M^{Mσ}/d^M_{Mσ}) = ∑_{r≥1} ℓ_r(x) t^r`, `ℓ_r = (1/4r)[S_{2r}(2M+1) − S_{2r}(M+σ)/u₊^{2r} − S_{2r}(M−σ)/u₋^{2r}]`, `S_{2r}(p) = 2B_{2r+1}((p+1)/2)/(2r+1)`, `t = N⁻²`; `κ_r = [t^r] exp(∑ ℓ_s t^s)` | `seedRatio`, `seedEll` (`ℓ_r = seedEll α β r x`, `α = M−σ`, `β = M+σ`), `Phi3j_eq_wignerSmallDx_mul_seedRatio`, `Phi3j_div_wignerSmallDx`, `wignerSmallDx_extremal`, `Phi3j_log_hasSum`, `Phi3j_log_hasUniformExpansionOn`, `Phi3j_ratio_hasUniformExpansionOn`; exact-in-`t` core `seedRatio_log_hasSum`, `seedRatio_log_hasUniformExpansion(_compact)`, `seedRatio_hasUniformExpansion(_compact)`, `Ct_log_hasSum`, `Ct_sq_eq_prod`, `Ct_pos_le`, `seedEll_one`; Bernoulli identity `centeredPowerSum_even_eq_bernoulliFun`; every chamber (`P2SeedAllChambers`): `Phi3j_eq_wignerSmallDx_mul_seedRatio_all`, `Phi3j_div_wignerSmallDx_all`, `Phi3j_log_hasSum_all`, `Phi3j_log_hasUniformExpansionOn_all`, `Phi3j_ratio_hasUniformExpansionOn_all`, `seedOK_of_lattice_all`, `wignerSmallDx_L0_eq`; **link to the local calculus (`prop:localcalculus`(b), `eq:3jpsi2r`)**: `f3even_zero_eq_expCoeff_mul`, `kap_apply_eq_expCoeff`, `seed_multiplier_link`, `allorder_operators_seed_multiplier`, `allorder_operators_seed_psi`, `seed_G1_formula`, with `exists_grid_point`, `grid_coeff_unique`, `continuousOn_expCoeff` | `P2SeedLogAllOrderPhys`, `P2SeedLogAllOrder`, `P2CtLogSeries`, `Asymptotics/CenteredPowerSum`, `Asymptotics/ExpExpansion`, `P2SeedMultiplierLink`, `P2SeedGridUnique`, `P2SeedAllChambers` | seed `k = 0` (`L = L₀`). `P2SeedLogAllOrderPhys` is the extremal chamber `M ≥ |σ|` (`α = M−σ`, `β = M+σ` natural, `L = M`); **every chamber** is `P2SeedAllChambers`: for `α = |M−σ|`, `β = |M+σ|` natural, `L₀ = max(|M|,|σ|)` and every `Lat4` lattice point, `Φ_{L₀}^{Mσ} = d^{L₀}_{Mσ}(x)·seedRatio α β x N⁻²` exactly with the same `seedRatio`/`seedEll` (`Phi3j_eq_wignerSmallDx_mul_seedRatio_all`, `Phi3j_div_wignerSmallDx_all`, `Phi3j_log_hasSum_all`, `Phi3j_log_hasUniformExpansionOn_all`, `Phi3j_ratio_hasUniformExpansionOn_all`, `seedOK_of_lattice_all`; the chamber enters only through `α, β` and the sign `seed3` of `d`; the source is `Phi3j_carrier_start`, which already contains `Phi3j_regge`/`Phi3j_neg_M`, so no further covariance argument is needed). The statements below about `(M, σ)` are for the extremal chamber unless marked `_all`. **Exact, stronger than a formal series:** at *every* physical lattice point `(N, μ)` (`a = j_-+m_-`, `c = j_++m_+` natural) the series `∑_{r≥1} ℓ_r(x)N^{-2r}` converges (all hypotheses `u_± > 0`, `α²t ≤ 4u₋²`, `β²t ≤ 4u₊²`, `(2M+1)²t ≤ 4` hold automatically) and its sum is `log(Φ/d)` (`Phi3j_log_hasSum`), `x = 2μ/N`, `d = wignerSmallDx M M σ` (nonzero on `(-1,1)`). Asymptotic form: on the physical grid, uniformly for `x` in a compact `K ⊆ (-1,1)`, `log(Φ/d)` has the `HasUniformExpansionOn` expansion `∑ ℓ_r N^{-2r}` and `Φ/d` has `∑ κ_r N^{-2r}`, `κ_r = expCoeff (seedEll α β) r` = the coefficient of `t^r` in the formal `exp(∑ ℓ_s t^s)` (`∑_{n≤r} (n!)⁻¹ [t^r] (∑ ℓ_s t^s)^n`; `κ_1 = ℓ_1`, `κ_2 = ℓ_2 + ℓ_1²/2`, `expCoeff_one/two`). The printed formula agrees with the exact seed (no sign or normalisation discrepancy); `S_{2r}(p)` is `centeredPowerSum p (2r)`, and the Bernoulli identity holds for all `p, r ∈ ℕ` (incl. `r = 0`, `p = 0`). **The multiplier link (formalised, `P2SeedMultiplierLink`):** for `α = M−σ`, `β = M+σ` natural (all of `M ≥ |σ|`, `M = 0` included) the order-`r` Taylor coefficient of the exact germ at the seed row is `f_{2r}^{(0)}(x) = κ_r(x) d^M_{Mσ}(x)` on `(-1,1)` (`f3even_zero_eq_expCoeff_mul`; proved by identifying two expansions of the same `Φ_M^{Mσ}` on the physical grid, using that the lattice is dense in `x` and unbounded in `N`, `exists_grid_point`/`grid_coeff_unique`), hence `(𝒢_r d_M)(x) = κ_r(x) d_M(x)` for the operators of `thm:3jallorderlocal` (`seed_multiplier_link`, `allorder_operators_seed_multiplier`) and, for `M > 0`, the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` has the multiplier `ψ_{r+1} = κ_{r+1} − 𝒥(𝖡_{r+1})d_M/d_M` (a smooth function on `(-1,1)`, `allorder_operators_seed_psi`: the paper's `eq:3jpsi2r`); `(𝒢_1 d_M)/d_M = ℓ_1 = (1/4)[S_2(2M+1) − S_2(β)/u₊² − S_2(α)/u₋²]` (`seed_G1_formula`). **Not formalised:** rationality of `ψ_{2r}`, the operator link `f_{2r}^{(0)} = κ_r d` outside the extremal chamber `M ≥ |σ|` (it needs the density of the physical lattice in `x`, `exists_grid_point`, proved only for `M ≥ |σ|`; the exact seed ratio itself is proved in every chamber, see above; `M = σ = 0` is the case `α = β = 0`, where `ℓ_r = 0`), higher ranks `k > 0`, uniformity up to `x = ±1` (the `ℓ_r` have poles at `u_∓ = 0` only when `α ≥ 2`, resp. `β ≥ 2`, since `S_{2r}(0) = S_{2r}(1) = 0`, so the expansion cannot be uniform up to the corresponding endpoint in that case) |
| `thm:6jallorderlocal`, `lem:6jseedrational` | | | **not formalised** |

### Weyl P3: exact finite and algebraic identities (`FormalResearch/Racah/P3*.lean`)

Paper: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex` (T) and `weyl_midpoint_semiclassics_appendices.tex` (A). Only the exact finite/algebraic identities, the Wigner-ladder contact identity and the abstract Jacobi-chain comparison below are formalised; all Airy, Darboux/WKB, adiabatic-transfer, mesoscopic and quantum-`6j` content of Paper III is not (no Airy function or uniform asymptotic theory in Mathlib or here). All headline theorems depend only on `[propext, Classical.choice, Quot.sound]`. They are built on the P2 modules above (`Phi_disccomplete`, `Phi6_completeness`, `Phi3j_nlo_expansion`, `a6_one_closed`, `Phi6_nlo_expansion`).

| paper statement | Lean | file | note |
|---|---|---|---|
| **`rem:flux-gauss`**, exact part (T), `3j`: `λ² = N`, `λ² w = 2`, `w = 2/N` | `gaussWeight_3j`, `lambdaSq3j`, `xLat_centred_gap` | `P3FluxGauss` | `λ² = ∑_L (2L+1) Φ_L(x_n)²` (natural gauge `Ŷ = √(2L+1)Φ`), every node `n < K`, all `N` with `SpecAdm M σ N`; `w = x_{n+1} - x_n`, equal to the centred gap. Corollary of `Phi_disccomplete` |
| **`rem:flux-gauss`**, exact part (T), `6j`: `λ² = 4AB/(2C)`, `λ² w = 2`, `w = C/(AB)` | `SixJ.gaussWeight_6j`, `SixJ.lambdaSq6j`, `SixJ.omegaW_eq_C_div`, `SixJ.omegaW_eq_centred_gap` | `P3FluxGauss` | under `RacahSystem a b m n D`, every physical `c_i`; `C = wC c = c + 1/2`. `w` is `omegaW = ω_c` (the cell width `x̂(c) - x̂(c+1)`, `omegaW_eq_cell_width`), which equals the centred gap `(x_{c-1} - x_{c+1})/2` of the nodes `x_c = cosA A B (wC c)`. Corollary of `Phi6_completeness` |
| `rem:flux-gauss`, **not formalised** | | | the semiclassical step `J_phys(x_j) = λ_j² w_j(1+O(h³))/4` (open in the paper), the quantum `6j` deformed identity and `δ_fl = -1/12`, the truncated-chain control |
| **`cor:3j-phase-exactness`**, fixed-rank datum `c(x) = -J₂(0,x)` (A, proof "the fixed-rank datum"; T `eq:phase-exactness-J20`, `eq:hahn-J20`) | `hahn_datum_alg`, `hahn_datum`, `Phi3j_datum_expansion` with the definitions `rho20` (`eq:general-rho20`), `J20` (`eq:phase-exactness-J20`), `Q2` (`𝒬_{2,k}` of the proof of `prop:general-fixed-rank-contact`) | `P3PhaseDatum` | **algebraic datum identity**: P2's `t`-coefficient `(A₂d'+B₂d)/(12(x²-1))` (`nloF2`, `thm:3jNLO`) `= 𝒬_{2,L}[d] - J₂(0,x) d` for Hahn data `eq:hahn-class-data`, all `L, M, σ`, `x ∈ (-1,1)`; `Phi3j_datum_expansion` is the same on the lattice `3j` with the `O(N⁻⁴)` remainder of `Phi3j_nlo_expansion`. `rho20`, `J20`, `Q2` are copied from the paper as definitions: their derivation from the Darboux/WKB expansion, and the identification of the pullback's `t`-coefficient with `√(2k+1) 𝒬_{2,k} d_k`, are not formalised. Natural-gauge factor `√(2k+1)` omitted |
| **`cor:6j-phase-exactness`**, fixed-rank datum `c(x) = -J₂(0,x)` for the centered Racah chain (A; `eq:racah-class-data`) | `racah_datum`, `a6_datum`, `Phi6_datum_expansion` | `P3PhaseDatum` | same: `G_{f,2} = P_f d' + Q_f d` (`nlo6G`, `thm:6jclosedcorrection`) `= 𝒬_{2,f}[d] - J₂(0,x) d` with `ε₁ = ρ`, `β₁ = w/4`, `β₂ = (1/2-m²-n²)w/8`, `χ₆ = ρx - w/4`, `λ₁ = 0`, `ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`, for all real `(f, m, n, ρ, w)`; `a6_datum` for the exact `t`-coefficient `a6 f m n 1`, `Phi6_datum_expansion` for the exact `6j` symbol with `(α, β) = (A, B)` and remainder `C S⁻⁴` |
| **`lem:racah-cayley-menger`**, `eq:racah-cayley-menger` (T:1622; A "Proof of Lemma `lem:racah-cayley-menger`" and the two remarks after it) | `cmDet_racah_poly`, `cmDet_racah_T`, `heron`, `cmDet_racah_D6` (both forms of `D₆`), `D6adiab_eq_D6lin`, `volume_formula`, `cmDet_pos_iff`/`cmDet_eq_zero_iff`/`cmDet_neg_iff`, `faces_admissible`, `volume_sq`, `volume_sq_le`, `volume_sq_max_iff`, `cmDet_equilateral`, `cmRacah_homog` (namespace `FormalResearch.Racah.P3`) | `P3CayleyMenger` | exact polynomial identity for the `5×5` Cayley--Menger determinant (`Matrix.det`) of `(Nα,Nβ,Nγ;Nβ,Nα,Nρ)`: `= 2N⁶ρ²(4α²β²-(α²+β²-γ²)²-γ²ρ²) = 8N⁶ρ²α²β² D₆ = 2N⁶ρ²(16T²-γ²ρ²)` (`T² = s(s-α)(s-β)(s-γ)`), all reals; sign trichotomy for `N,α,β,ρ ≠ 0`; `288𝒱² = det` for the paper's `𝒱 = F r_A r_B sin ω/6` as an identity of squares; the volume/equilateral remarks. **Extra**: `D₆ > 0` already forces `ρ < 2α, 2β` (the face admissibility the proof leaves implicit). Not formalised: `det CM = 288𝒱²` for an actual Euclidean tetrahedron, the existence criterion, Schläfli/dihedral angle `ω = Θ_F` |
| **`prop:general-fixed-rank-contact`**, contact identity `eq:general-contact-identity` (T:650; A:475-503); `eq:wigner-natural-jacobi` (T:249) | `contact_identity` (all ranks `k ≥ 1/2`, `|a|,|b| ≤ k`), `contact_identity_exceptional` (`a = b = k = 0`), `contact_identity_hahn`, `contact_identity_racah`, `wigner_natural_jacobi`, `wigner_natural_jacobi_zero`, `contact_residual_hasDerivAt`, `Q2_beta2_part`, `Q2_lam1_part`, `contact_alg` (gauge-free core) | `P3ContactIdentity` | the `t`-coefficient of the residual of `Û^{[2]}` vanishes: `x û_k - A_{k+1}û_{k+1} - A_kû_{k-1} - B_kû_k = -ε₁[(k+1)²A_{k+1}d̂_{k+1} + k²A_kd̂_{k-1}] + (β₁κ²+β₂+λ₁x)d̂_k` with `û_j = √(2j+1)𝒬_{2,j}d_j`, natural gauge, `A0`, `B0` as in `eq:wigner-natural-jacobi`; from `wignerSmallDx_rank_lower/upper` only. Edge row `k_min` and `k = 1/2` automatic (`R_{k_min} = 0`, `√0 = 0`); `a = b = k = 0` separate. `contact_residual_hasDerivAt`: with the first-order jets of `A_j(t)`, `B_k(t)`, `Û_j(t)` as hypotheses, the residual is `0` at `t = 0` with derivative `0`. `rho20`, `Q2` are the paper's definitions (`P3PhaseDatum`): the derivation of `û_k` as the `t`-coefficient of the pullback is not formalised |
| **`prop:forbidden-decay`** (a),(b) (T:1008; A "Hyperbolicity and the physical solution on the forbidden side"), **`prop:exact-hyperbolicity`** (T:996) and `(F1)`-`(F3)`, `eq:forbidden-slope`, `eq:forbidden-const-ratio` | `backward_ratio`, `etilde_concaveOn`, `etilde_antitone`, `etilde_le_one`, `Phi_convexOn`, `forbidden_slope`, `Psi_plus_concaveOn`, `Psi_minus_convexOn`, `Psi_minus_monotoneOn`, `Psi_plus_deriv_zero`, `etilde_hasDerivAt_zero`, `hyperbolic_of_slope`, `F_le_cosh_etilde`, `rr_sub_one_le`, `Bk_close`, `exact_hyperbolicity_hahn_racah` (namespace `FormalResearch.Racah.P3`) | `P3JacobiComparison` | abstract order argument: backward ratio recursion under a constant-ratio supersolution (`y = 1`: (a); general `y`: (b), `y ≤ 1` not needed); concavity of `ẽ` (geometric mean; any real `p,q`); `Φ = τ(x-β₀σ)-ẽ` convex for both signs so `Φ(σ) ≥ κ(σ-σ_*)`; `prop:exact-hyperbolicity` for Hahn/Racah for the closed forms `A_k = ½r_kẽ(σ_k)`, `B_k` with the paper's explicit constants `ρ₁, ρ₂, C₀`. Not formalised: the quantum-`6j` variant, the verification part of (b) (`D`, the product), (c), the sharper exponential decay of (b), and everything involving `Θ`, `ξ`, Airy beyond the Discrete-to-Airy subsection of the Airy section (the identification of the closed forms with the integer-data `3j/6j` chains, `prop:hahn-class`, `prop:racah-class`, is `hahn_class_chain`, `racah_class_chain` there; the monotone decay (a) to the hard edge is `hd_backward_decay`, `hr_hardedge_decay`) |
| **not formalised** (Paper III) | | | everything else, in particular `thm:general-phase-exactness` and the `O(N⁻³)` phase-exact pullback, the derivation of `ρ₂(0,x)`/`𝒬_{2,k}` from the second-order Weyl density, all Airy statements, `thm:general-critical`, `thm:general-mesoscopic`, the quantum `6j` (`sec:q6j`), `lem:q6j-recurrence`, `prop:D2D4match` |

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
| Centred power sums `S_n(p) = ∑_{q=-(p-1)/2}^{(p-1)/2} q^n`: `S_{2r}(p) = 2B_{2r+1}((p+1)/2)/(2r+1)` (all `p, r ∈ ℕ`), `S_{odd} = 0`, `\|S_n(p)\| ≤ p(p/2)^n`, `S_2 = p(p²-1)/12` | `centeredPowerSum`, `bernoulli_telescope`, `centeredPowerSum_even_eq_bernoulliFun`, `centeredPowerSum_odd`, `abs_centeredPowerSum_le`, `centeredPowerSum_two` (`Asymptotics/CenteredPowerSum`) |
| Mercator series of a finite product: `∑_i log(1-y_i) = -∑_{n≥1}(∑_i y_i^n)/n` for `\|y_i\| < 1` | `hasSum_log_one_sub_finset` (`Asymptotics/LogSeries`) |
| A convergent series `∑ t^r a_r(z)` with `\|a_r(z)\| ≤ C q^r` on `K` is a `HasUniformExpansion` (`ε = id`) | `hasUniformExpansion_of_hasSum_geom` (`Asymptotics/GeometricExpansion`) |
| `exp` of an expansion with `a_0 = 0` is an expansion with the coefficients `κ_r = [X^r] exp(∑ a_s X^s)` of the formal exponential (`ε → 0`); real-valued only | `HasExpansionAlong.exp`, `HasUniformExpansion.exp`, `expSeries`, `expCoeff`, `coeff_expSeries_eq_sum`, `expCoeff_one`, `expCoeff_two` (`Asymptotics/ExpExpansion`) |
| P2 central products: exact convergent series `log Ct r u t − r log u = −∑_{n≥1} S_{2n}(r)(t/u²)^n/(2n)` for `u > 0`, `t ≥ 0`, `r²t ≤ 4u²`; `Ct² = ∏(u² − q²t)` | `Ct_log_hasSum`, `Ct_sq_eq_prod`, `Ct_pos_le` (`Racah/P2CtLogSeries`); the coefficients agree with `Ct_log_expansion_two` (`-r(r²-1)/24`) at `n = 1` |
| P2 extremal seed, `eq:3jseedlogallorder` | see the Weyl P2 local calculus table (`P2SeedLogAllOrder*`) |

Third-party input: the Euler–Maclaurin formula and the Stirling series for `log Γ` (`log_gamma_em`), vendored without modification from `girving/interval` (Apache-2.0). Location: `ThirdParty/interval/`; see its `NOTICE.md`.

### Hard edge / Mehler–Heine (`FormalResearch/Asymptotics/DominatedSeries.lean`, `FormalResearch/Special/JacobiMehlerHeine*.lean`, `JacobiBessel.lean`, `LaguerreHardEdge.lean`)

Infrastructure for the Laguerre/Bessel hard-edge statements of Weyl P2 (`weyl_midpoint_recoupling.tex`, section "Laguerre hard edges": `prop:LaguerreEdge`, `thm:6jhardedge`, `rem:Laguerre`; `eq:WignerJacobiMonic`). Only the classical Jacobi/Bessel limit and the exact Laguerre recurrence are formalised; the paper's discrete Hahn/Racah edge statements (the `[1+O(N^{-2})]` ratio `Φ/d = R_{p,r}[…]`, the `3j`/`6j` kernels at the edge points, the lower corner) are **not**. All headline theorems depend only on `[propext, Classical.choice, Quot.sound]`.

| Statement | Lean | Notes |
|---|---|---|
| Uniform Tannery theorem for finite sums with varying index sets: terms converge uniformly on `K`, tail terms dominated by a summable `M` ⟹ `∑_{ℓ∈s i} F_i,ℓ → ∑' G_ℓ` uniformly on `K`; pointwise case; rate version (`≤ (∑D + ∑ℓM_ℓ)/n`) | `tendstoUniformlyOn_sum_of_dominated`, `tendsto_sum_of_dominated`, `norm_sum_sub_tsum_le_of_rate` (`DominatedSeries`) | generic; the `ε/4` splitting into head, tail of the finite sum, tail of the limit |
| **Mehler–Heine** (Szegő 8.1.1, DLMF 18.11.1): `n^{-α} P_n^{(α,β)}(cos(z/n)) → ∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))`, uniformly for `‖z‖ ≤ R` (or `z` in any bounded `K ⊆ ℂ`) | `mehlerHeine_uniform`, `mehlerHeine_uniformOn_bounded`, `mhLimit`, `tendsto_mhCoeff`, `abs_mhCoeff_le`, `mh_aeval` (`JacobiMehlerHeine`) | real `α > -1`, arbitrary real `β`; from the explicit sum `jacobi` (DLMF 18.5.7) and `cos w - 1 = -2 sin²(w/2)`: termwise limit by `GammaRatio.gamma_ratio_isEquivalent`, explicit majorant `e^α (e(2+|α+β+1|))^ℓ/ℓ!`; the polynomial is evaluated at the complex point by `Polynomial.aeval` |
| the same with a remainder `O(1/n)`, uniformly for `‖z‖ ≤ R` (`C, N` not explicit) | `mehlerHeine_rate`, `mehlerHeine_rate_isBigO` (`JacobiMehlerHeineRate`) | exact factorisation `mhCoeff = A_ℓ · P · W · G` (`mhCoeff_eq`), `|G-1| ≤ c/n` from `GammaRatio.gamma_ratio_two_term` (`mhG_bound`) |
| link to Mathlib: `Complex.besselJ α z = (z/2)^α · mhLimit α z` (every real `α`), `mhLimit α z = regularizedHGFun 0 {α+1} (-(z/2)²)`; Mehler–Heine in Bessel form `→ (z/2)^{-α} J_α(z)` uniformly on bounded `K ⊆ ℂ ∖ {0}` | `mhLimit_eq_regularizedHGFun`, `besselJ_eq_cpow_mul_mhLimit`, `mhLimit_eq_cpow_neg_mul_besselJ`, `mehlerHeine_besselJ` (`JacobiBessel`) | Mathlib defines `besselJ` through `regularizedHGFun`; the identification with the series `∑ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))` is `mhLimit_eq_regularizedHGFun` |
| real-argument forms: `(jacobi α β n).eval (cos (x/n))` uniformly on bounded `K ⊆ ℝ`, with rate `C/n` on `|x| ≤ R`; `J_α(x)` real for `x > 0` | `mehlerHeine_real`, `mehlerHeine_real_rate`, `besselJ_ofReal`, `mhLimitReal_eq_rpow_mul_besselJ_re` (`JacobiBessel`) | |
| `rem:Laguerre`, `eq:Lagrec`: the orthonormal Laguerre Jacobi recurrence `√(n(n+p))Ξ_{n-1} + √((n+1)(n+p+1))Ξ_{n+1} = (2n+p+1)Ξ_n` has the solution (including its `n = 0` row; uniqueness up to scale is not formalised) `Ξ_n = √((n+1)_p) = √(Γ(n+p+1)/n!)` (`p > -1`; Pochhammer form for natural `p`) | `laguerre_recurrence`, `laguerreRegular`, `laguerreRegular_nat` (`LaguerreHardEdge`) | exact algebraic identity |
| leading part of the exact magnetic difference equation `eq:3jdiff` at `x = 1 - h(p+1+2n)` as `h → 0⁺`: `a_h(x±h)/(4h) → √(n(n+p))`, `√((n+1)(n+p+1))`, `2(1-x²)/(4h) → 2n+p+1`, so the equation applied to `Ξ` tends to `0` | `ah3`, `edgePoint`, `ah3_upper_tendsto`, `ah3_lower_tendsto`, `diag_tendsto`, `laguerre_limit_edge_equation` (`LaguerreHardEdge`) | `a_h` is the paper's `eq:ah3` transcribed (`p = |M-σ|`, `q = |M+σ|`); **not** formalised: that the physical `3j` symbol solves it (`Φ(1-hy) = h^{p/2}Ξ(y;h)`), the passage from the coefficient limits to the asymptotics of the solution, the `6j` `c`-lattice version |

### Airy function (`FormalResearch/Special/Airy*.lean`, aggregate `FormalResearch.Special.Airy`)

Infrastructure for the Airy connections of Weyl P3 (`weyl_midpoint_semiclassics.tex`, `thm:general-rank-airy`) and the free-fermion edge (`Weyl/free_fermion`, `thm:edge`, Airy kernel); no paper statement is formalised here, only the function and its basic theory. Mathlib has no Airy function. `Ai(z) = (1/2π) ∫_ℝ exp((1+is)³/3 − z(1+is)) ds` on `ℂ` (`airyAiC`), absolutely convergent (Gaussian decay in `s`, locally uniformly in `z`); `airyAi : ℝ → ℝ` is its real restriction. All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms` at the end of each module). **Not formalised:** the full asymptotic series (the `AiryAsym*` rows give the first term with explicit remainder, `AiryAsymChi` the `u_1` term, `AiryZeroSecondOrder{Saddle,Chi}` the `u_2` term for `Ai`, `Bi` on the negative axis; not `u_3` and higher), the `-(5/36)t^{-4}` coefficient of the zeros' expansion and the zeros of `Ai'` (DLMF 9.9.19) (the second order DLMF 9.9.18 of `a_n` is proved, with non-sharp constants), sharp constants, the asymptotics of the general Clark nodes `z_n(α)` (`α ≢ 0, π/2`), the `Ai'` and `P·Ai+Q·Ai'` versions of the good-circle lower bound (E2) and so of the residue-defect formula and Clark-Airy summation for `ψ_α` (the pure-`Ai` case is formalised: subsection *CFT consequences of the Airy zeros* below), Theorem Q for `ν ∈ [−1, 1/2]`, the products for `Ai'` and `Bi` (the Hadamard product of `Ai` itself is formalised: section *Complex analysis: Hadamard factorization* below), Olver's own `N` and the crossing point `c = −0.366…` (`airyCross > −1`), Olver uniform expansions, the Mellin moments `∫_0^∞ x^{s−1}Ai`, the first zero of `Bi` and `Bi > 0` beyond `−11/10`, and the open parts of the discrete-to-Airy chain (`κ` and `κ ≠ 0`, the single normalisation `|Y_{k₁}| ≤ δ^{-p}` of the closed-form chains, the non-recessive `Ai/Bi` pair and the full oscillatory side, uniformity over families and the existence of lattice nodes, half-integer chain data, the Racah `q_*` derivation and the `τ = -1` branch, explicit constants, analyticity of the Langer coordinate: see the subsection *Discrete-to-Airy limit* below).

| Statement | Lean | Notes |
|---|---|---|
| kernel `exp(t³/3 − z t)`, `t = c + is`: `‖·‖ = exp(c³/3 − Re z·c + Im z·s − c s²)`; uniform Gaussian majorants; integrability and decay of the polynomial multiples `(−t)^k K`; `∂_s K = i(t²−z)K`; FTC identity `∫ P_{k+2} = z ∫ P_k + k ∫ P_{k−1}` | `airyKernel`, `airyPoly`, `norm_airyKernel`, `norm_airyPoly_le`, `integrable_airyPoly`, `tendsto_airyPoly`, `integral_airyPoly_succ_succ` (`AiryKernel`) | `c > 0`; the identity is integration by parts in `s` |
| `Ai` entire; `∂_z M_k = M_{k+1}` (differentiation under the integral, `M_k = (1/2π)∫(−t)^k K`); `Ai^{(k)} = M_k(1,·)`; **`Ai'' = z Ai` on `ℂ`**; derivative recurrence `Ai^{(k+3)} = z Ai^{(k+1)} + (k+1) Ai^{(k)}` (`Ai^{(k+3)}(0) = (k+1)Ai^{(k)}(0)`) | `airyMom`, `airyAiC`, `hasDerivAt_airyMom`, `differentiable_airyAiC`, `deriv_airyAiC`, `hasDerivAt_deriv_airyAiC`, `iteratedDeriv_two_airyAiC`, `iteratedDeriv_airyAiC`, `iteratedDeriv_airyAiC_succ_succ_succ` (`AiryDef`) | domination by `dominated_loc_of_deriv_le` with explicit majorants |
| **contour independence**: `M_k(c,z)` does not depend on `c > 0` | `airyMom_indep`, `hasDerivAt_airyMom_c` (`AiryDef`) | proved by `∂_c M_k = 0` (Cauchy–Riemann `∂_c = −i∂_s` plus the FTC identity), not by Cauchy's theorem |
| real forms: `conj Ai(z) = Ai(conj z)`, `Ai(x), Ai'(x)` real; `Ai'' = xAi` on `ℝ`; `Ai ∈ C^∞(ℝ)` | `conj_airyAiC`, `airyAiC_ofReal`, `airyAi`, `airyAi'`, `hasDerivAt_airyAi`, `hasDerivAt_airyAi'`, `iteratedDeriv_two_airyAi`, `contDiff_airyAi` (`AiryReal`) | |
| **forbidden-side decay**, `x > 0`: `\|Ai(x)\| ≤ (1/(2√π)) x^{−1/4} e^{−(2/3)x^{3/2}}`, `\|Ai'(x)\| ≤ (1/(2π))(√π x^{1/4} + x^{−1/2}) e^{−(2/3)x^{3/2}}` | `airyAi_abs_le`, `airyAi'_abs_le`, `norm_airyMom_zero_le`, `norm_airyMom_one_le` (`AiryBound`) | take `c = √x` in the contour-independent representation |
| identities for any solution of `y'' = xy` (`ℝ` or `ℂ`): Wronskian constant, `(xy² − y'²)' = y²`, kernel diagonal limit `K(x,x) = y'² − xy²`, `(∂_x+∂_t)K = −y(x)w(t)`; ODE uniqueness along `ℝ` (complex values): `y(0)=y'(0)=0 ⇒ y ≡ 0`, and determination by `(y(0), y'(0))` | `IsAirySol`, `IsAirySol.wronskian_const`, `.hasDerivAt_energy`, `.tendsto_airyKernelXY_diag`, `.hasDerivAt_airyKernelXY_shift`, `airy_unique_real`, `airy_eq_of_initial` (`AiryEquation`) | independent of the definition of `Ai`; uniqueness is Mathlib's `ODE_solution_unique_of_mem_Ioo` on `ℂ × ℂ` |
| `Ai, Ai', xAi² − Ai'² → 0` at `+∞`; `∫_x^∞ Ai² = Ai'(x)² − x Ai(x)²` for every real `x`; Airy kernel `airyKernelAi`, `K(x,t) → Ai'(x)² − xAi(x)²`, `(∂_x+∂_t)K = −Ai(x)Ai(t)` | `isAirySol_airyAi`, `isAirySol_airyAiC`, `tendsto_airyAi`, `tendsto_airyAi'`, `tendsto_airyAi_energy`, `integral_Ioi_airyAi_sq`, `airyKernelAi_diag`, `airyKernelAi_shift` (`AiryIdentities`) | |
| lower bound `Ai(x) ≥ (1/(2√π))x^{−1/4}e^{−(2/3)x^{3/2}}(1 − 5/(48x^{3/2}))`, hence `2√π x^{1/4}e^{(2/3)x^{3/2}}Ai(x) → 1`; **`Ai > 0` and `Ai' < 0` on `[0,∞)`**, `Ai` strictly decreasing there | `airyAi_lower_bound`, `airyAi_asymptotic`, `airyAi_pos`, `airyAi'_neg`, `strictAntiOn_airyAi` (`AiryPositive`) | `c = √x`, `cos u ≥ 1 − u²/2`, Gaussian moments; no zero on `[0,∞)` from `(Ai·Ai')' = Ai'² + xAi² ≥ 0` and decay (no Airy-specific value of `Ai(0)` used) |
| **all zeros of `Ai` are real and negative** | `airyAiC_zero_real_neg` (`AiryZeros`) | `y(x) = Ai(z₀+x)`, `∫_0^∞ (ȳy')' = 0` gives `z₀∫\|y\|² = −(∫\|y'\|² + ∫x\|y\|²)`; `∫\|y\|² > 0` by the identity theorem; exponential decay along the ray from the `c = 1` representation |
| `Ai(z) + ωAi(ωz) + ω²Ai(ω²z) = 0` (`ω = e^{2πi/3}`); `Bi(z) = e^{iπ/6}Ai(ωz) + e^{−iπ/6}Ai(ω²z)`: entire, `Bi'' = zBi`, real on `ℝ`; Wronskian `Ai Bi' − Ai' Bi` constant `= −2√3 Ai(0)Ai'(0) > 0` | `airyAiC_rotation`, `airyBiC`, `isAirySol_airyBiC`, `conj_airyBiC`, `airyBiC_ofReal`, `airyBi`, `airyAiC_wronskian_airyBiC`, `airyWronskian_pos` (`AiryRotation`) | rotation from ODE uniqueness on `ℝ` plus the identity theorem; `ω`, `ε = e^{iπ/6}` are written algebraically (`airyOmega_eq_exp`, `airyEps_eq_exp` link them to `exp`) |
| **exact values**: `Ai(0) = 3^{−2/3}/Γ(2/3)`, `Ai'(0) = −3^{−1/3}/Γ(1/3)`, `Ai(0)Ai'(0) = −1/(2√3 π)`; **`W(Ai,Bi) = Ai Bi' − Ai' Bi = 1/π`** on `ℂ`; `Bi(0) = 3^{−1/6}/Γ(2/3)`, `Bi'(0) = 3^{1/6}/Γ(1/3)` | `airyAi_zero`, `airyAi'_zero`, `airyAi_mul_airyAi'_zero`, `airyWronskian_eq`, `airyAiC_wronskian_airyBiC_eq`, `airyBi_zero`, `airyBiC'_zero_eq` (`AiryValues`) | contour rotation to the rays `arg t = ±π/3` without Cauchy: for `w(τ) = (τ²+i√3)/2`, `∂_τ [w G_k(c+rw)] = τ ∂_r[r G_k(c+rw)]`, so `∫_0^∞ w G_k(c+rw) dr` is constant in `τ ∈ [0,1]` (`hasDerivAt_airyRayInt_zero`; Gaussian majorant uniform in `τ` because `c > 0`: the rate is proportional to `c`), then `c → 0⁺` (dominated convergence) and Mathlib's Gamma integral `∫ r^k e^{−r³/3}` + reflection `Γ(1/3)Γ(2/3) = 2π/√3` (`airyMom_one_zero_re`, `integral_pow_exp_cube`) |
| **Taylor series**: `Ai(z) = Ai(0)F(z) + Ai'(0)G(z)` with `F = Σ A_j z^{3j}/(3j)!`, `G = Σ B_j z^{3j+1}/(3j+1)!`, `A_j = ∏_{i<j}(3i+1)`, `B_j = ∏_{i<j}(3i+2)`; both series converge on all of `ℂ`; `F'' = zF`, `G'' = zG`, `F(0)=1, F'(0)=0, G(0)=0, G'(0)=1`; projections `3Ai(0)F(z) = Σ_{ζ³=1} Ai(ζz)`; explicit `Ai = 3^{−2/3}/Γ(2/3)·F − 3^{−1/3}/Γ(1/3)·G` | `airyAiC_eq_taylor`, `hasSum_airyTaylorF`, `hasSum_airyTaylorG`, `isAirySol_airyTaylorF`, `isAirySol_airyTaylorG`, `airyTaylorF_eq`, `airyTaylorG_eq`, `airyTaylorF_zero`, `airyTaylorG_zero`, `airyAiC_eq_explicit` (`AiryTaylor`) | from the Taylor expansion of the entire function `Ai` (`Complex.hasSum_taylorSeries_of_entire`) split by exponent mod 3 (`Nat.sumByResidueClasses`), using `Ai^{(k+3)}(0) = (k+1)Ai^{(k)}(0)`; not by ODE uniqueness |
| **Laplace/Fourier side**: `∫_ℝ Ai(x)e^{ax}dx = e^{a³/3}` for `Re a > 0` (absolutely convergent: `\|e^{cx}Ai(x)\| ≤ K e^{−(c/2)\|x\|}`); real case; `∫ Ai(x)e^{εx−iωx}dx = e^{(ε−iω)³/3} → e^{iω³/3}` (`ε → 0⁺`, Abel-regularised `∫Ai(x)e^{−iωx}dx = e^{iω³/3}`); `∫Ai(x)e^{εx}dx → 1` | `integral_airyAi_mul_exp_complex`, `integral_airyAi_mul_exp`, `integrable_airyTilt`, `integrable_airyAi_mul_exp`, `tendsto_integral_airyAi_fourier`, `tendsto_integral_airyAi_mul_exp` (`AiryFourier`) | `e^{cx}Ai(x)` is `𝓕` of `s ↦ exp((c+2πis)³/3)` (the definition of `Ai` with substitution `s ↦ 2πs`); Mathlib's `Continuous.fourierInv_fourier_eq`; no conditionally convergent integral is formalised |
| **free-parameter bound on `ℂ`**: for every `c > 0`, `‖Ai(z)‖ ≤ (1/(2π))√(π/c) exp(c³/3 − c Re z + (Im z)²/(4c))`; `Ai'` analogue with factor `(c + \|Im z\|/(2c))√(π/c) + 1/c`; `c = Re w` for `z = w²` gives exactly `exp(−(2/3) Re w³)` | `airy_norm_le_free_param`, `airy_deriv_norm_le_free_param`, `airyParamExp`, `airyParamExp_sq`, `airy_sq_norm_le_sqrt` (`AiryEnvelopeParam`, `AiryEnvelopeSector`) | completing the square in `s` in `norm_airyKernel`; `‖t‖ ≤ c + \|s\|` |
| **(E1) complex envelope, all of `ℂ`** (principal `z^{3/2}`; `Re z^{3/2} = 0` on the negative axis): `‖Ai(z)‖ ≤ 3(1+\|z\|)^{−1/4} exp(−(2/3) Re z^{3/2})`; **(E1′)** `‖Ai'(z)‖ ≤ 5(1+\|z\|)^{1/4} exp(−(2/3) Re z^{3/2})`; order `3/2`: `‖Ai(z)‖ ≤ 3 exp((2/3)\|z\|^{3/2})` (and `Ai'`); squared: `‖Ai(z)‖² ≤ 9(1+\|z\|)^{−1/2} e(z)`, `e = airyEnv = exp(−(4/3) Re z^{3/2})` | `airyAiC_envelope`, `airyAiC_deriv_envelope`, `airyAiC_norm_le_exp_rpow`, `airyAiC_deriv_norm_le_exp_rpow`, `airyAiC_norm_sq_le`, `airyEnv`; root-coordinate forms `airy_sq_envelope`, `airy_deriv_sq_envelope` (`AiryEnvelope`, `AiryEnvelopeBound`) | `z = w²`, `Re w ≥ 0`: `\|w\| ≤ 1` by `c = 1`; `Re w ≥ \|w\|/2` (`\|arg z\| ≤ 2π/3`) by `c = Re w`; the rest by the rotation identity and its derivative (`airyAiC_rotation_deriv`), `(ωz)^{3/2} = z^{3/2}`, `(ω²z)^{3/2} = −z^{3/2}`. Constants `3`, `5` not optimal (mpmath sup of the `Ai` ratio over `\|z\| ≤ 30` is `≈ 0.64`, of the `Ai'` ratio `≈ 0.54`). **The envelope calculus, the monotonicity of `e` and the good-circle lower bound are the (E3) and (E2) rows below. Not formalised there: the `Ai'` and `P·Ai+Q·Ai'` versions of the good-circle bound |
| **`Ai > 0` on `[−1, ∞)`**, `Ai(x) ≥ Ai(0) cos x` on `[−1, 0]`; **two-sided real envelope** (`lem:airy2-recessive`(i) input; part (ii), Olver's `M`, `E` and `Bi`, is in the `AiryOlver*`, `AiryBi*` rows below; the amplitude `Ai²+Bi²` for `y ≥ 1` is in the `AiryAsym*` rows) for `X ≥ −1`: `(1/20)(2+X)^{−1/4}e^{−ξ(X)} ≤ Ai(X) ≤ 4(2+X)^{−1/4}e^{−ξ(X)}`, `ξ = (2/3)(max X 0)^{3/2}`; `\|Ai'(X)\| ≤ 120(2+X)^{1/2} Ai(X)` | `airyAi_pos_Icc`, `airyAi_ge_on_Icc`, `airyAi_pos_of_neg_one_le` (`AiryEnvelopeNeg`), `airyAi_envelope_real`, `abs_airyAi_le_real`, `airyAi_ge_real`, `abs_airyAi'_le_mul_airyAi`, `airyXi`, `re_ofReal_cpow_three_halves` (`AiryEnvelopeReal`) | Sturm-type: `H = Ai' cos + Ai sin` has `H' = (1+x)cos x · Ai`, so `Ai/cos` is antitone while `Ai ≥ 0`; first-zero argument by compactness; lower bound on `[1,∞)` is `airyAi_lower_bound`, on `[0,1]` monotonicity with `Ai(1) ≥ 1/9`. Does not locate the first zero `≈ −2.338` (it is located in `(−2.35, −2.33)` by `airy_exists_zero_first`, `AiryFirstZeros`, see the ordered-zeros rows); constants not optimal (`≈ 0.28`/`0.55` true, mpmath on `[-1, 20]`). The P3 `lem:airy2-recessive` statement is for `[−1,∞)` with `Ai > 0`, `Ai ≍ (2+X)^{−1/4}e^{−ξ}`, `\|Ai'\| ≤ C(2+X)^{1/2}Ai`: all three now hold here (constants aside) |
| **Airy kernel as a Gram integral** (real `x, y`): `K(x,y) = ∫_0^∞ Ai(x+t)Ai(y+t) dt`, absolutely convergent, `K(x,x) = Ai'² − xAi²`; `K` symmetric, `K(x,x) = ∫_x^∞ Ai² > 0`, `K(x,y)² ≤ K(x,x)K(y,y)`, measurable | `airyKer`, `airyKer_eq_integral`, `integrableOn_airyAi_shift_mul`, `airyKer_comm`, `airyKer_diag_nonneg`, `airyKer_diag_pos`, `airyKer_quad`, `airyKer_sq_le`, `measurable_airyKer` (`AiryKernelOpFormula`) | off the diagonal: integrate the shift identity `(∂_x+∂_y)K = −Ai(x)Ai(y)` using `K(x+s,y+s) → 0`; diagonal: `integral_Ioi_airyAi_sq`; `K²≤K K` is the discriminant of `∫(Ai(x+t)+λAi(y+t))²`. real arguments (complex: next row) |
| **Complex arguments**: `K(x,y) = ∫_0^∞ Ai(x+t)Ai(y+t) dt` for all `x, y ∈ ℂ` (real `t`, absolutely convergent; `K = (Ai(x)Ai'(y) − Ai'(x)Ai(y))/(x−y)`, `K(x,x) = Ai'² − xAi²`); symmetric; agrees with `airyKer` on `ℝ`; `K(x, x̄) = ∫_0^∞ \|Ai(x+t)\|² dt ≥ 0` | `airyKerC`, `airyKerC_eq_integral`, `integrableOn_airyAiC_shift_mul`, `airyKerC_comm`, `airyKerC_ofReal`, `airyKerC_conj`, `airyKerC_conj_nonneg` (`AiryKernelOpComplex`) | same proof as the real case, with the exponential decay of `Ai(z₀+t)`, `Ai'(z₀+t)` along real shifts (`airyRay_decay`, `AiryZeros`) and `conj Ai(z) = Ai(z̄)`. **Not formalised:** the growth bound `\|K(x,x̄)\| ≲ (1+\|x\|)^{1/2}e(x)` (needs sector bounds on `Ai`) |
| diagonal: `K' = −Ai²` (antitone); `K(x,x) ≤ Ai'(x)² ≤ ((1/(2π))(√π x^{1/4}+x^{−1/2})e^{−(2/3)x^{3/2}})²` for `x>0`; **elementary growth bound `K(x,x) ≤ K(−1,−1)(1+x_−)`** | `hasDerivAt_airyKer_diag`, `antitone_airyKer_diag`, `airyKer_diag_le_sq`, `airyKer_diag_le` (`AiryKernelOpBounds`) | `Ai²+Ai'²/\|x\|` is nondecreasing on `x<0` (derivative `Ai'²/x²`) so `K(x,x) ≤ \|x\|K(−1,−1)` for `x ≤ −1`. **Not proved:** the the sharp `(1+x_−)^{1/2}` is the next row (`AiryKernelOpSharp`) |
| **`N_Ai(u) = ∫_u^∞ K(s,s)ds = (2u²Ai(u)² − 2uAi'(u)² − Ai(u)Ai'(u))/3`** (W1 `eq:Aimean`); `∫_u^∞ Ai'² = (u²Ai² − uAi'² − 2AiAi')/3`; `N_Ai(u) ≤ (N_Ai(0)+K(−1,−1))(1+u_−)²`, `∫_u^∞Ai'² ≤ (R(0)+K(−1,−1))(1+u_−)²` | `airyN`, `airyR`, `integral_Ioi_airyKer_diag`, `integrableOn_Ioi_airyKer_diag`, `integral_Ioi_airyAi'_sq`, `integrableOn_Ioi_airyAi'_sq`, `airyN_le`, `integral_Ioi_airyAi'_sq_le`, `tendsto_pow_mul_airyAi_sq`, `tendsto_pow_mul_airyAi'_sq` (`AiryKernelOpBounds`) | differentiate the closed forms using `Ai'' = xAi`; decay of `u^nAi²`, `u^nAi'²` from `airyAi_abs_le`, `airyAi'_abs_le`. Exponent `2` here; the sharp `3/2` is the next row (`AiryKernelOpSharp`) |
| **Operator `K_u` on `L²(u,∞)`** (integral statements only): Hilbert–Schmidt `∫∫_{(u,∞)²}K² ≤ N_Ai(u)²` (finite), trace `∫_u^∞K(s,s)ds = N_Ai(u)`, self-adjoint (symmetric kernel), positive semidefinite: `∫∫ g(x)K(x,y)g(y) = ∫_0^∞(∫ g(x)Ai(x+t)dx)²dt ≥ 0` for `g` measurable, bounded, compactly supported (so for continuous compactly supported `f` on `(u,∞)`) | `integrable_airyKer_sq`, `integral_airyKer_sq_le`, `integral_integral_airyKer_sq_le`, `airyKer_quadForm_eq`, `airyKer_quadForm_nonneg`, `airyKer_quadForm_nonneg_Ioi` (`AiryKernelOpOperator`) | Fubini on `(x,y,t)`. **Not formalised:** `K_u` as a bounded operator (operator norm), `K_u = A_uA_u^*` as operators, trace-class norm, eigenvalue decay, Fredholm determinant (Mathlib has no such theory) |
| **sharp diagonal exponents** (W1 `edge_crossover`): `K(x,x) ≤ 34(1+x_-)^{1/2}`, `N_Ai(u) ≤ 28(1+u_-)^{3/2}`, `∫_u^∞ Ai'² ≤ 22(1+u_-)^{3/2}` for all real `x`, `u` (from the complex envelope on the negative axis: `\|Ai x\| ≤ 3(1+\|x\|)^{-1/4}`, `\|Ai' x\| ≤ 5(1+\|x\|)^{1/4}`) | `airyKer_diag_le_sqrt`, `airyN_le_sharp`, `integral_Ioi_airyAi'_sq_le_sharp`, `abs_airyAi_le_of_nonpos`, `abs_airyAi'_le_of_nonpos` (`AiryKernelOpSharp`) | explicit constants; the exponents are the sharp ones (the weaker exponents 1, 2 of `AiryKernelOpBounds` are superseded). The leading asymptotics `K(-y,-y) = √y/π + O(1/y)` for `y ≥ 1` are `airyKer_diag_neg` (`AiryAsymReal`); not formalised: the matching lower bounds for all `x` |

| **Exact saddle-point formula**: for `Re w > 0`, `Ai(w²) = (e^{−(2/3)w³}/(2π)) ∫_ℝ exp(−w s² − i s³/3) ds` and `Ai'(w²) = −(e^{−(2/3)w³}/(2π))(w∫ e^{−ws²−is³/3} + i∫ s e^{−ws²−is³/3})` (substitution `t = w + is` on the line `Re t = Re w`, using `airyMom_indep` only for real `c`) | `airyAiC_sq_eq`, `deriv_airyAiC_sq_eq`, `airyMom_sq_eq`, `airyPoly_shift` (`AiryAsymSaddle`) | proved; axioms `[propext, Classical.choice, Quot.sound]` |
| **Second-order saddle-point estimate**, every `w` with `ρ = Re w > 0`: `‖Ai(w²) − (e^{−(2/3)w³}/(2π))(π/w)^{1/2}‖ ≤ (1/(2π))‖e^{−(2/3)w³}‖ (5/48)√(π/ρ)/ρ³` (`= (5/(96√π))‖e^{−(2/3)w³}‖ρ^{−7/2}`), and the analogue for `Ai'` with `‖w‖(5/48)√(π/ρ)/ρ³ + (1/4)√(π/ρ)/ρ²` | `norm_airyAiC_sq_sub_le`, `norm_deriv_airyAiC_sq_add_le`, `norm_saddleJ0_sub_le`, `norm_saddleJ1_le`, `norm_exp_I_mul_sub_one_sub_le` (`AiryAsymSaddle`) | proved (Gaussian moments `∫s⁶e^{−ρs²}`, `∫s⁴e^{−ρs²}`, `‖e^{ix}−1−ix‖ ≤ x²/2`); no Olver theory; only the first term of the expansion, `Re w > 0` only |
| **`Ai`, `Ai'`, `Bi` on the negative axis** (DLMF 9.7.9–9.7.11 with explicit first remainder), all `y > 0`, `ξ = (2/3)y^{3/2}`: `\|Ai(−y) − π^{−1/2}y^{−1/4}cos(ξ−π/4)\| ≤ y^{−7/4}/8`, `\|Ai'(−y) − π^{−1/2}y^{1/4}sin(ξ−π/4)\| ≤ (2/5)y^{−5/4}`, `\|Bi(−y) + π^{−1/2}y^{−1/4}sin(ξ−π/4)\| ≤ y^{−7/4}/8` | `airyAi_neg_asymptotic`, `airyAi'_neg_asymptotic`, `airyBi_neg_asymptotic` (`AiryAsymReal`); `r = √y` forms `airyAi_neg_sq_asymptotic`, `airyAi'_neg_sq_asymptotic`, `airyBi_neg_sq_asymptotic`, rotation `airyAi_neg_eq`, `deriv_airyAiC_rotation` (`AiryAsymNeg`) | proved from the saddle estimate at `w = √y e^{iπ/6}` (`w³ = i y^{3/2}`, `\|e^{−(2/3)w³}\| = 1`) and the rotation identity; constants are those of the proof (numerically the errors are `≤ 0.5×` these); not the full series, not `Bi'` |
| **Amplitude and kernel diagonal on the negative axis**, `y ≥ 1`: `\|Ai(−y)² + Bi(−y)² − 1/(π√y)\| ≤ (2/5)y^{−2}`; `\|K(−y,−y) − √y/π\| ≤ 1/y` with `K(x,x) = Ai'(x)² − xAi(x)²` (relative error `O(y^{−3/2})`) | `airyAi_sq_add_airyBi_sq_neg`, `airyKer_diag_neg` (`AiryAsymReal`) | proved from the three asymptotics above (`abs_sq_sub_sq_le` and explicit arithmetic) |
| **Positive axis**, `x > 0`: `\|Ai(x) − P(x)\| ≤ (5/48)x^{−3/2}P(x)`, `P = (1/(2√π))x^{−1/4}e^{−(2/3)x^{3/2}}`; `\|Ai'(x) + (1/(2√π))x^{1/4}e^{−(2/3)x^{3/2}}\| ≤ (17/(96√π))x^{−5/4}e^{−(2/3)x^{3/2}}` | `airyAi_sub_leading_le`, `airyAi'_add_leading_le`, `airyAi'_sq_add_leading_le` (`AiryAsymPos`) | proved (`Ai`: from `airyAi_lower_bound`, `airyAi_abs_le`; `Ai'`: saddle estimate at real `w = √x`); not `Bi` |
| **Zeros of `Ai` far on the negative axis (window form; the labelling `k = n − 1` is the phase-of-the-`n`-th-zero row below)**: if `y ≥ 4` and `Ai(−y) = 0` there is `k ∈ ℤ` with `\|(2/3)y^{3/2} − (k+3/4)π\| ≤ (2/5)y^{−3/2}`; for every integer `k ≥ 2` there is exactly one `y > 0` with `Ai(−y) = 0` and `\|(2/3)y^{3/2} − (k+3/4)π\| < π/3` (DLMF 9.9.6 with `k = n−1`) | `airy_zero_location`, `airy_zero_window_existsUnique` (`AiryAsymZeros`); `r = √y` forms `airy_zero_location_r`, `airy_zero_window_existsUnique_r`, `airy_zero_window_exists`, `window_no_two` | proved (sign of `Ai` where `\|cos φ\| ≥ 1/2`, `Ai' ≠ 0` where `\|sin φ\| ≥ 1/2`, intermediate value theorem and Rolle); the labelling (that the `n`-th zero `a_n` has `k = n − 1`) is `airyZero_phase` (`AiryZeroLabel`); **not proved:** the `5/(48t²)` correction |
| **Improper integrals** `∫_0^∞ Ai = 1/3` (DLMF 9.10.11), `∫_{−∞}^0 Ai = 2/3` (convergent, not absolutely), `∫_{−∞}^∞ Ai = 1` (`Ai` is Lebesgue integrable on `(0,∞)` only): `∫_{(0,∞)} Ai = 1/3`; `∫_0^T Ai → 1/3`, `∫_{−T}^0 Ai → 2/3` (`T→∞`), `∫_{−S}^T Ai → 1` (`S,T→∞` independently) | `integral_Ioi_airyAi`, `tendsto_integral_airyAi_zero_top`, `tendsto_integral_airyAi_bot_zero`, `tendsto_integral_airyAi_interval`, `tendsto_integral_airyAi_symm`, `integrableOn_airyAi_Ioi`, `airyAiPrim`, `airyAiPrim_rotation`, `norm_airyAiPrim_ray_sub_le`, `airyAiPrim_neg_eq`, `tendsto_airyInt_neg`, `airyIntPos_eq` (`AiryIntegral`, `AiryIntegralArc`); generic `tendsto_integral_mul_exp_neg_of_tendsto` (`AiryAbel`) | entire primitive `P` of `Ai` (Morera); integrate the rotation identity at `z=−y` ⇒ `∫_{−y}^0Ai = P(ye^{iπ/3})+P(ye^{−iπ/3}) → 2L`, `L=∫_0^∞Ai`, because the arc `{ρe^{±iθ}, 0≤θ≤π/3}` contributes `≤ 3π/(2√ρ)` by the complex envelope `‖Ai‖≤3e^{−(2/3)Re z^{3/2}}` and Jordan's `cos φ ≥ 1−2φ/π`; then Abel's theorem applied to `∫Ai e^{εx}=e^{ε³/3}→1` gives `3L=1`. No asymptotics of `Ai` on the negative axis used. mpmath: `∫_0^{60}Ai=1/3` (30 digits). **Not formalised:** `Ai ∉ L¹(−∞,0)`, rate of convergence, one-sided Laplace transform (no closed form) |
| `F(z) = 0F1(; 2/3; z³/9)`, `G(z) = z·0F1(; 4/3; z³/9)` (DLMF 9.4.1–9.4.2, Mathlib's *regularized* `0F1`, `0F1(;b;w) = Γ(b) regularizedHGFun 0 {b} w`); `Ai(z) = 3^{−2/3} rHG_{2/3}(z³/9) − 3^{−4/3} z rHG_{4/3}(z³/9)` | `airyTaylorF_eq_hyp`, `airyTaylorG_eq_hyp`, `airyAiC_eq_hyp` (`AiryHypergeometric`); helpers `airyFactorial_three_mul`, `gamma_two_thirds_add`, `gamma_four_thirds_add`, `regularizedHGFun_zero_singleton`, `airyCoefA_succ`, `airyCoefB_succ` | coefficient identities `(3j)! = A_jB_j3^j j!`, `Γ(2/3+j)=Γ(2/3)B_j/3^j`, `Γ(4/3+j)=Γ(4/3)A_{j+1}/3^j`; checked with mpmath at `z=0.7, −2.3, 1+2i` (`10^{−31}`). Mathlib has no ordinary `0F1`, hence the regularized form |
| **`K_u` bounded self-adjoint positive on `L²(u,∞)` (function level, no `Lp` operator)**, `(K_uf)(x) = ∫_u^∞K(x,y)f(y)dy`: for measurable `f` with `∫_u^∞f²<∞`: `(K_uf)(x)² ≤ (∫_u^∞K(x,y)²dy)∫f²` for every `x`; `K_uf ∈ L²(u,∞)` and **`∫_u^∞(K_uf)² ≤ N_Ai(u)² ∫_u^∞f²`**; the form `B_u(g,f)=∫∫g(x)K(x,y)f(y)` converges absolutely with `B_u(g,f)² ≤ N_Ai(u)²∫g²∫f²`, is symmetric `B_u(g,f)=B_u(f,g)`, and **`B_u(f,f) ≥ 0` for every `f∈L²`** | `airyKerOp`, `airyKerOp_sq_le`, `integral_airyKerOp_sq_le`, `measurable_airyKerOp`, `airyKerForm`, `airyKerForm_sq_le`, `airyKerForm_comm`, `airyKerForm_self_nonneg`, `airyKerOp_cs` (general Cauchy–Schwarz), `integrable_airyKerForm` (`AiryKernelOpL2`) | CS via the discriminant; `|K(x,y)| ≤ √K(x,x)√K(y,y)` + trace; positivity by `L²`-truncation `f·1_{(u,n]∩{|f|≤n}}` and the existing compact-support `airyKer_quadForm_nonneg`. **Not formalised:** `K_u` as an element of `Lp ℝ 2 →L[ℝ] Lp ℝ 2` (Mathlib has no Hilbert–Schmidt / integral-operator API; the `Lp` packaging would need AE-class bookkeeping only), `K_u=A_uA_u^*`, trace-class norm, spectrum, Fredholm determinant |
| **Abel-regularised orthogonality of Airy translates** (regularisation of DLMF 9.11.15 `∫Ai(x+s)Ai(x+t)dx=δ(s−t)`; `Ai∉L²`): for `ε>0`, `∫_ℝAi(x)Ai(x+t)e^{εx}dx = exp(ε³/12 − εt/2 − t²/(4ε))/(2√(πε))`; `t=0`: `∫Ai²e^{εx}dx = e^{ε³/12}/(2√(πε))`; for `t≠0` the limit `ε→0⁺` is `0` | `integral_airyAi_mul_airyAi_shift`, `integral_airyAi_sq_mul_exp`, `tendsto_integral_airyAi_mul_airyAi_shift`, `airyGram_four_tilt`, `airyGram_trans`, `airyGram_fourier`, `airyGram_tilt` (`AiryGram`) | Mathlib's multiplication formula `∫𝓕f·g=∫f·𝓕g` with `e^{cx}Ai(x)=𝓕(h_c)` (`AiryFourier`), Fourier inversion, translation phase, and the Gaussian FT (`(c+is)³+(c−is)³=2c³−6cs²`: cubic terms cancel). mpmath: three `(ε,t)` agree to ≥15 digits. The brief's guess `∫Ai(x)Ai(x+t)=2^{−1/3}Ai(2^{−1/3}t)` is **false** (that is not an orthogonality relation); the true value is `δ(t)`. **Not formalised:** distributional statement with test functions, unitarity on `L²`, `K_Ai²=K_Ai` |
| **(E3) envelope calculus**: for every `u ∈ ℂ`, real `τ` (survey: `τ ≥ 0`): `e(u+τ) ≤ e(u) exp(−2τ Re√u)` (`e = airyEnv`); `e(u) ≤ e(u')` if `Re u = Re u'`, `\|Im u\| ≤ \|Im u'\|`, so `e(x+is)` is nondecreasing in `s ≥ 0` (AIRY_POISSON (E3), LOCAL_AIRY_MODEL (c)) | `airyEnv_add_real_le`, `airyEnv_mono_im`, `airyEnv_mono_of_nonneg`, `re_cpow_three_halves_add_ge`, `airySqrtRe` (`AiryEnvCalculus`) | `w = u^{1/2} = a+ib`: `Re u^{3/2} = a³−3ab² = 3(Re u)a − 2a³`; the shift inequality is the identity `Re(u+τ)^{3/2} − Re u^{3/2} − (3/2)τa = (a'−a)²(a'+a/2) + (3/2)a(b'−b)²` using only `ab = a'b'`, `a,a' ≥ 0`; monotonicity from `a² = (‖u‖+Re u)/2`. mpmath (30 digits, 2·10⁴ random points): no violation, min relative slack `1.6e-7` |
| **(E4)**: `Φ_τ(u) = Ai(k(u+τ))`, `k = 2^{2/3}` (`k^{3/2} = 2`); for `τ ≥ 0`: `‖Φ_τ(u)‖ ≤ 3(1+τ)^{1/4}(1+‖u‖)^{−1/4} e(u) exp(−2τ Re√u)` | `airyPhi`, `airyPhiK`, `airyPhi_norm_le`, `re_cpow_three_halves_dilate`, `cpow_three_halves_ofReal_mul` (`AiryEnvCalculus`) | from (E1) (`airyAiC_envelope`), `Re (kv)^{3/2} = 2 Re v^{3/2}`, `1+‖u‖ ≤ (1+τ)(1+‖u+τ‖)`, (E3). Constant `3` from (E1); mpmath sup of the ratio is `0.29`. Only the pointwise bound (not the distributional Poisson identities of AIRY_POISSON Thm 1) |
| **Sector asymptotics with relative remainder** (DLMF 9.7.5/9.7.6, explicit constants): `0<s≤1`, `Re w ≥ s‖w‖`: `‖Ai(w²) − L(w)‖ ≤ (5/48)/(s³√s‖w‖³)‖L(w)‖`, `L(w) = (1/2π)e^{−(2/3)w³}(π/w)^{1/2}`; `‖Ai'(w²) + wL(w)‖ ≤ (17/48)/(s³√s‖w‖³)‖wL(w)‖`; z-form (`Re z ≥ (2s²−1)‖z‖`, i.e. `\|arg z\| ≤ π − 2arccos s`): `‖Ai(z) − Λ(z)‖ ≤ (5/48)/(s³√s‖z‖^{3/2})‖Λ(z)‖`, `‖Λ(z)‖² = e(z)/(4π√‖z‖)`; lower bound: if `(5/48)/(s³√s‖z‖^{3/2}) ≤ 1/2` then `‖Ai(z)‖² ≥ e(z)/(16π√‖z‖)` | `norm_airyAiC_sq_sub_lead_le`, `norm_deriv_airyAiC_sq_add_lead_le`, `airyLead`, `airyAiLead`, `airyAiDerivLead`, `airyAiC_sector_asymptotic`, `deriv_airyAiC_sector_asymptotic`, `norm_airyAiLead_sq`, `norm_airyAiDerivLead_sq`, `airyAiC_sq_ge_sector` (`AiryAsymSector`) | the saddle estimate holds for every `Re w > 0`; on the sector `ρ = Re w ≥ s‖w‖` turns it into `O(‖w‖^{−3}) = O(|z|^{−3/2})`. mpmath (30 digits, `s ∈ {1/2, 0.2588, 0.8}`, 41 angles over the whole sector, `‖w‖ ∈ [0.5,20]`): actual/stated ≤ `0.47` (`Ai`), `0.22` (`Ai'`) |
| **`Ai` near the negative axis, complex phase** (DLMF 9.7.9 with explicit remainder): `q ≠ 0`, `Re q ≥ (√3/2)‖q‖` (`\|arg q\| ≤ π/6`, i.e. `\|arg(−q²)\| ≥ 2π/3`), `ξ = (2/3)q³`: `‖Ai(−q²) − (1/π)(π/q)^{1/2}cos(ξ − π/4)‖ ≤ (6/5)e^{\|Im ξ\|}(√(π/‖q‖)/π)/‖q‖³` | `airyAiC_neg_complex`, `airyAiC_neg_sq_rotation`, `airyLead_eps_mul`, `airyLead_conj_eps_mul`, `airyLead_sum_eq`, `NegSector` (`AiryAsymNegComplex`) | rotation `Ai(−q²) = −ωAi((ε̄q)²) − ω²Ai((εq)²)` (no branch of `(−z)^{1/4}` needed), sector estimate with `s = 1/2` for both terms, `(π/(ε^{±1}q))^{1/2} = e^{∓iπ/12}(π/q)^{1/2}` (equal squares, positive real parts since `Re τ² > 0`). mpmath: error ≤ `0.087`·bound (61 angles, `‖q‖ ∈ [0.5,40]`). Real-axis case is `airyAi_neg_asymptotic`; **not formalised:** the `Ai'` (sine) analogue |
| **Good circles (E2)**: for every `k ≥ 10` there is `r ∈ [k,k+1]` with `(2/3)r^{3/2} ∈ π/4 + πℕ` such that for all `‖u‖ = r`: `‖Ai(u)‖² ≥ (1/(25π))(1+r)^{−1/2} e(u)`; in particular `Ai ≠ 0` on the circle (GENERAL_THEOREMS Lemma 1.0, α = 0; LOCAL_AIRY_MODEL "good circles") | `good_circle_exists`, `good_circle_airyAiC_ne_zero`, `good_radius_exists`, `airyAiC_neg_sq_ge`, `airyNorm_cos_good`, `airyEnv_neg_sq` (`AiryGoodCircles`) | `Re u ≥ −‖u‖/2`: sector lower bound (`s = 1/2`); else `u = −q²` and the complex two-exponential formula with `\|cos(ξ−π/4)\| ≥ e^{\|Im ξ\|}/4` (`‖ξ‖ = π/4 + mπ`, `Re ξ ≥ 0`: if `\|Im ξ\| ≥ 1` from `\|e^{iw}\|, \|e^{−iw}\|`, else `\|cos x\| cosh y`, `x = mπ − d`, `0 ≤ d ≤ 1`), and `e(−q²) = e^{2\|Im ξ\|}`. mpmath (20 digits, `k = 10..59, 80, 120, 160, 200`, 721 angles): min of `‖Ai‖²/((1+r)^{−1/2}e)` is `0.0798 ≈ 1/(4π)`, so `1/(25π) = 0.0127` is conservative. Not formalised: `ψ_α = cosα Ai − sinα Ai'` and `P·Ai + Q·Ai'` (Lemma 1.0, 1.0′; need the `Ai'` analogue of `airyAiC_neg_complex`); these circles feed `airy_defect_bound` / `airy_quadrature` below |
| **Connection formulas and the Hermite–Biehler ratios** (DLMF 9.2.10): `Bi(z) − iAi(z) = 2ε̄ Ai(ω²z)`, `Bi(z) + iAi(z) = 2ε Ai(ωz)`; for `Im u ≥ 0`: `Re(ω²u)^{3/2} = −Re u^{3/2}`, `e(ω²u) = e(u)^{−1}`, `‖Bi − iAi‖² ≤ 36(1+‖u‖)^{−1/2}/e(u)`; on a good circle `‖(Bi−iAi)/Ai‖·e ≤ 30√π` (`Im u ≥ 0`), `‖(Bi+iAi)/Ai‖·e ≤ 30√π` (`Im u ≤ 0`): the `\|R_±\| ≤ C/e` input of the defect formula (AIRY_POISSON Thm D; the formula itself is `airy_defect_bound` in the subsection *CFT consequences of the Airy zeros*) | `airyBiC_sub_I_mul_airyAiC`, `airyBiC_add_I_mul_airyAiC`, `re_cpow_three_halves_omega_sq`, `airyEnv_omega_sq`, `airyEnv_conj`, `norm_airyBiC_sub_I_mul_sq_le`, `airy_Rplus_bound`, `airy_Rminus_bound`, `good_circle_ratio_bounds` (`AiryRatioBounds`) | `Ai + ωAi(ω·) + ω²Ai(ω²·) = 0` with the definition of `Bi`; principal root `(ω²u)^{1/2} = e^{−iπ/3}u^{1/2}` (positive real part for `u ≠ 0`, `Im u ≥ 0`); lower half plane by conjugation. `30√π ≈ 53` vs numerical `C_0 ≈ 2.01` (mpmath: `2.012` at `r = r_10`, tends to `2`): the constants are products of `3`, `1/(25π)`, `2` |
| `Bi'` on the real axis: `Bi'' = x Bi`, `Bi, Bi'` real, real Wronskian `Ai Bi' - Ai' Bi = 1/π` | `airyBiDeriv`, `hasDerivAt_airyBi`, `hasDerivAt_airyBiDeriv`, `airyWronskian_real`, `conj_airyBiC'` (`AiryBiReal`) | from the complex rotation definition; real forms of the complex identities |
| **`Bi'` on the negative axis** (DLMF 9.7.10 first term): `\|Bi'(-y) - π^{-1/2} y^{1/4} cos(ξ - π/4)\| ≤ (2/5) y^{-5/4}`, `ξ = (2/3) y^{3/2}` | `airyBiDeriv_neg_asymptotic` (`AiryAsymBiNeg`) | single saddle at `w = r e^{i π/6}`, rotation `Bi' = e^{i π/6} ω Ai'(ω z) + conj`; constant of the proof; every `y > 0` |
| **`Bi`, `Bi'` on the positive axis** (DLMF 9.7.7, 9.7.8 first terms): `\|Bi(x) - π^{-1/2} x^{-1/4} e^{ξ}\| ≤ (4/5) x^{-7/4} e^{ξ}`, `\|Bi'(x) - π^{-1/2} x^{1/4} e^{ξ}\| ≤ (7/4) x^{-5/4} e^{ξ}` | `airyBi_pos_asymptotic`, `airyBiDeriv_pos_asymptotic` (`AiryAsymBiPos`) | `Bi = 2 Re(e^{i π/6} Ai(ω x))` with the exact saddle formula at `w = r e^{i π/3}` (`w^3 = -r^3`, so the exponential is real); constants of the proof; every `x > 0` (informative for `x ≳ 1`) |
| **`χ = Ai + i Bi` with `u_1 = 5/72`** (DLMF 9.7.9-9.7.11 to first correction): `\|Ai(-y) + i Bi(-y) - π^{-1/2} y^{-1/4} e^{-i θ}(1 + i (5/72)/ξ)\| ≤ (1/5) y^{-13/4}`, `θ = ξ - π/4` | `airyChi_neg_asymptotic`, `norm_airyAiC_sq_third_le`, `norm_saddleJ0_third_le`, `airyAiC_add_I_mul_airyBiC` (`Ai + i Bi = 2 e^{i π/3} Ai(ω^2 z)`) (`AiryAsymChi`, `AiryAsymChiAux`) | third-order saddle estimate: fourth-order Taylor remainder of `e^{-i s^3/3}`, exact complex Gaussian moments `int s^6 e^{-w s^2}`, `int s^12`; remainder is the order of `u_2` (`u_2 = 385/10368`, numerically `\|rem\| y^{13/4} ≤ 0.0472`); constant `1/5` non-optimal; the `u_2` term itself is in the `AiryZeroSecondOrder` rows below |
| `Ai`, `Bi` to order `u_1` and first terms of `χ`, `χ'` | `airyAi_neg_asymptotic_u1` (`\|Ai(-y) - π^{-1/2} y^{-1/4}(cos θ + (u_1/ξ) sin θ)\| ≤ (1/5) y^{-13/4}`), `airyBi_neg_asymptotic_u1` (`... ((u_1/ξ) cos θ - sin θ)`), `airyChi_neg_asymptotic_first`, `airyChi'_neg_asymptotic_first` (`AiryAsymChi`) | corollaries of `airyChi_neg_asymptotic`; `χ'` only to first order |
| **`Bi/Ai` strictly increasing on `[-1, ∞)`**, `Bi ≥ √3 Ai` and `Bi > 0`, `Bi' > 0` on `[0, ∞)`, `Bi` strictly increasing there | `strictMonoOn_airyBi_div_airyAi`, `airyBi_ge_sqrt3_mul_airyAi`, `airyBi_pos`, `airyBiDeriv_pos`, `strictMonoOn_airyBi_Ici` (`AiryBiMono`) | `(Bi/Ai)' = 1/(π Ai^2) > 0` from the Wronskian, `Ai > 0` on `[-1, ∞)`; `Bi(0) = √3 Ai(0)` (`AiryValues`) |
| **`Bi > 0` on `[-11/10, ∞)`**, `Bi ≥ 1/100` there, `Bi' > 0`, `Bi` strictly increasing | `airyBi_ge_on_Icc`, `airyBi_ge_one_hundredth`, `airyBi_pos_of_neg_eleven_tenth_le`, `airyBiDeriv_pos_of_ge`, `strictMonoOn_airyBi_Ici_neg` (`AiryBiNeg`) | ODE comparison (`Bi'' = x Bi`, Picard iterates) from `Bi(0) ≥ 0.599`, `Bi(0) Bi'(0) = √3/(2 π)`; numerics from `Γ(2/3) ≤ (√ π + 1)/2` (convexity of `Γ`); first zero of `Bi` is `-1.1737`, not reached |
| **two-sided envelope of `Bi` on `[-1, ∞)`**: `(1/800)(2+x)^{-1/4} e^{ξ} ≤ Bi ≤ 16 (2+x)^{-1/4} e^{ξ}`; `(1/16000)(2+x)^{-1/2} ≤ Ai Bi ≤ 64 (2+x)^{-1/2}`; `Bi' ≤ 5300 (2+x)^{1/2} Bi` | `airyBi_envelope_real`, `airyAi_mul_airyBi_envelope`, `airyBiDeriv_le_mul_airyBi` (`AiryBiEnvelope`) | `x ≥ 2` from the positive-axis asymptotics, `[-1,2]` from `1/100 ≤ Bi ≤ Bi(2)`; `Bi'` from the Wronskian and `\|Ai'\| ≤ 120 (2+x)^{1/2} Ai`; non-optimal constants (true ones about 0.28 and 0.9 for large `x`) |
| **Notation**: DLMF 9.8 modulus `M^2 = Ai^2 + Bi^2` (`airyModSq`), `N^2 = Ai'^2 + Bi'^2`; Wronskian `1/π^2 ≤ M^2 N^2` | `airyModSq`, `airyModDerivSq`, `one_div_pi_sq_le_airyModSq_mul` (`AiryOlver`) | Cauchy-Schwarz on the Wronskian |
| **Olver weights `E`, `M`** (crossing point `c`, `Ai = Bi`): `E = 1`, `M = (Ai²+Bi²)^{1/2}` for `x ≤ c`; `E = (Bi/Ai)^{1/2}`, `M = (2 Ai Bi)^{1/2}` for `x > c`; `E ≥ 1`, `E` nondecreasing, `E² = Bi/Ai`, `M/E = √2 Ai`, `M E = √2 Bi`, `\|Ai\| ≤ M/E`, `\|Bi\| ≤ M E`; **derivative weight `N`** with `\|Ai'\| ≤ N/E`, `\|Bi'\| ≤ N E` | `airyCross`, `airyOlverE`, `airyOlverM`, `airyDerivWeightN`, `one_le_airyOlverE`, `monotone_airyOlverE`, `airyOlverE_sq`, `airyOlverM_eq`, `airyOlverM_div_E`, `airyOlverM_mul_E`, `abs_airyAi_le_airyOlverM_div_E`, `abs_airyBi_le_airyOlverM_mul_E`, `abs_airyAi'_le_airyDerivWeightN_div_E`, `abs_airyBiDeriv_le_airyDerivWeightN_mul_E`, `airyAi_le_airyBi_of_ge`, `airyBi_lt_airyAi_of_lt` (`AiryOlver`) | `E`, `M` are Olver's functions (DLMF 9.8's `Ai²+Bi²` is a different function for `x > c`); `airyDerivWeightN` is **not Olver's `N`**: it is a convenient majorant, `(Ai'²+Bi'²)^{1/2}` for `x ≤ c` and `max(E\|Ai'\|, \|Bi'\|/E)` for `x > c`, discontinuous at `c` (`0.5345` from the left, `0.4820` from the right), and unrelated to `(−2Ai'Bi')^{1/2}`, which violates the two inequalities on `(c, c+0.016)`; `airyCross > −1` and `c = −0.36604…` not formalised, nothing uses them |
| **`E^2 ~ e^{2 ξ}` and `E^{-2} = Ai/Bi ~ e^{-2 ξ}/2`** for `x > c`: `(1/3200) e^{2 ξ} ≤ E^2 ≤ 320 e^{2 ξ}`; `\|2 e^{2 ξ} Ai/Bi - 1\| = O(x^{-3/2})`, `x ≥ 2` | `airyOlverE_sq_two_sided`, `airyAi_div_airyBi_asymptotic` (`AiryOlverBounds`) | from the envelopes and the first-term asymptotics of `Ai`, `Bi` (numerically `2 e^{2xi} Ai/Bi = 0.920, 0.981, 0.993, 0.998` at `x = 2, 5, 10, 20`) |
| **`M^2` two-sided on all of `ℝ`**: `(1/8000)/√(2+\|x\|) ≤ M^2 ≤ 600/√(2+\|x\|)` (Olver's `M`); on `x ≤ -1`: `(1/20)/√ y ≤ M(-y)^2 ≤ (3/4)/√ y` | `airyOlverM_sq_two_sided`, `airyOlverM_sq_neg_bounds`, `airyOlverM_sq_pos_bounds` (`AiryOlverBounds`) | negative side from the first-term asymptotics of `Ai, Ai', Bi, Bi'`, positive side from the envelopes; numerically `M^2 √(2+\|x\|) in [0.3235, 0.6366]` (limits `1/π`, `2/π`) |
| **`(M/E)^2`, `(M E)^2` for `x > c`**: `(1/200) e^{-2 ξ}/√(2+x) ≤ (M/E)^2 ≤ 32 e^{-2 ξ}/√(2+x)`; `e^{2 ξ}/(320000 √(2+x)) ≤ (M E)^2 ≤ 512 e^{2 ξ}/√(2+x)` | `airyOlverM_div_E_sq_bounds`, `airyOlverM_mul_E_sq_bounds` (`AiryOlverBounds`) | from `M/E = √2 Ai`, `M E = √2 Bi` and the envelopes |
| **`N ≤ C (2+\|x\|)^{1/2} M`** on all of `ℝ`, `C = 5300`, `N = airyDerivWeightN` | `airyDerivWeightN_le`, `airyDerivWeightN_le_of_neg_one_le` (`AiryOlverBounds`) | `x ≥ -1` from `\|Ai'\| ≤ 120 (2+x)^{1/2} Ai`, `Bi' ≤ 5300 (2+x)^{1/2} Bi`; `x < -1` from `N^2 ≤ 2 √ y` and the lower bound on `M^2`; numerically `N/((2+\|x\|)^{1/2} M) ≤ 0.98` |
| **Rational enclosures** `2.657 < Γ(1/3) < 2.691`, `1.326 < Γ(2/3) < 1.360`, hence `0.3533 < Ai(0) < 0.3628`, `−0.2611 < Ai'(0) < −0.2576` (true `0.355028…`, `−0.258819…`) | `airyGamma_add_nat`, `airyGamma_nat_add_le`, `airyGamma_nat_add_ge`, `airyGamma_enclosure`, `airyGamma_third_bounds`, `airyGamma_two_thirds_bounds`, `airyAi_zero_bounds`, `airyAi'_zero_bounds` (`AiryGammaBounds`) | Mathlib's `Real.BohrMollerup.f_add_nat_le/ge` for `log ∘ Γ` at `n = 27, 28` (powers `27^{1/3} = 3`, `27^{2/3} = 9` are integers) and `Γ(x+n) = Γ(x)∏(x+j)`; accuracy ≈ 1 %, not optimal; mpmath-checked |
| **Taylor evaluation at the first zero**: `Ai(−2.33) > 0 > Ai(−2.35)` (true `0.0056849`, `−0.0083388`); real form `Ai = Ai(0)F + Ai'(0)G` with `F = Σ A_j x^{3j}/(3j)!`, `G = Σ B_j x^{3j+1}/(3j+1)!`; tail bound `\|Σt − Σ_{k<K}t_k\| ≤ \|t_K\|/(1−ρ)` for geometric decay | `airyAi_eq_series`, `airyTail_abs_sub_le`, `airyFterm_ratio`, `airyGterm_ratio`, `airyF_enclosure`, `airyG_enclosure`, `airyAi_neg_233_pos`, `airyAi_neg_235_neg` (`AiryZeroTaylor`) | six exact partial sums (norm_num on rationals) + ratio `\|x\|³/((3k+2)(3k+3))` resp. `/((3k+3)(3k+4))`; the sign change holds for every `Ai(0)/\|Ai'(0)\| ∈ (1.287, 1.4325)` (true `1.3717`) |
| **Spacing of the zeros**: distinct zeros `x < x' ≤ 0` of `Ai` with `x ≥ −Y` satisfy `x' − x ≥ π/√Y`; Prüfer rate `θ(b) − θ(a) ≤ M(b−a)` for `−M ≤ a ≤ b`, `M ≥ 1` | `airy_zero_gap`, `airyGap_consecutive`, `airy_prufer_rate` (`AiryZeroGap`) | Prüfer levels `kπ < k'π` ⟹ consecutive zeros `x < x₁`; Sturm comparison with `y'' = −Y y`, `sin(√Y(x−c))`, `c` just below `x` (`IsSol.exists_zero_Icc_of_comparison`) |
| **Finite count**: `Ai(−4) < 0 < Ai(−4.84)`; `Ai > 0` on `[−2.33, 0]`; the zeros of `Ai` in `[−4.84, 0]` are exactly two, `a_1 ∈ (−2.35, −2.33)`, `a_2 ∈ (−4.84, −4)`; exactly one zero in `(−4, 0]`, exactly two in `(−4.84, 0]` | `airyAi_neg_four_neg`, `airyAi_neg_484_pos`, `airyAi_pos_of_neg_233_le`, `airy_exists_zero_first`, `airy_exists_zero_second`, `airy_zeros_Icc` (`AiryFirstZeros`); `airyZero_first_values`, `airyZero_one`, `airyZero_two`, `airyZero_three`, `airy_existsUnique_zero_Ioc_neg_four`, `airyZeroCount_neg_four`, `airyZeroCount_neg_484` (`AiryZeroOrder`) | `airyAi_neg_sq_asymptotic` at `r = 2, 2.2`; `θ(−2.33) ≥ θ(0) − 1 − 1.33·2.33 > −π` and `sin θ(−2.33) > 0`; third zero excluded by the spacing `π/2.2 > 1.427` (`Y = 4.84`) |
| **Ordered zeros** `a_1 > a_2 > …`: `airyZero n` is the unique zero `≤ 0` with exactly `n − 1` zeros in `(a_n, 0]`; strictly decreasing; every zero `z < a_n` is `≤ a_{n+1}`; every zero `≤ 0` is some `a_n` | `airyZeroSet`, `airyZeroCount`, `airyZeroCount_lt`, `exists_zero_count`, `airyZero`, `airyAi_airyZero`, `airyZeroCount_airyZero`, `eq_airyZero`, `airyZero_strictAnti`, `airyZero_next`, `exists_airyZero_eq`, `airyZero_lt_of_lt` (`AiryZeroOrder`) | count via `airy_zeros_ncard` / `airy_node_exists_unique` (Prüfer levels), no choice of lift enters the definition |
| **Phase of the n-th zero** (DLMF 9.9.6 with explicit remainder, offsets fixed): for `n ≥ 2`, `y = −a_n`: `\|(2/3)y^{3/2} − (n − 1/4)π\| ≤ (2/5)y^{−3/2}` (`r = √y`: `\|(2/3)r³ − (n−1/4)π\| ≤ (2/5)/r³`) | `airyZero_phase`, `airyZero_phase_r`, `airyZeroRoot`, `airyZero_phase_base`, `airyZero_phase_step` (`AiryZeroLabel`) | induction: base from the location theorem + numerical range of `a_2`; step: the window-`n` zero lies left of `a_n`, so is `≤ a_{n+1}`; label `n−1` excluded by window uniqueness (`n ≥ 3`) resp. `a_3 < −4.84` (`n = 2`). mpmath: `\|…\|·y^{3/2} ≤ 0.1042 → 5/48` (n ≤ 200), so `2/5` is not sharp |
| **Size and spacing of the zeros** (`n ≥ 2`): `4.08 n ≤ \|a_n\|^{3/2} ≤ 4.72 n`; `16 n² ≤ \|a_n\|³ ≤ 23 n²`; `2.5 n^{2/3} ≤ \|a_n\| ≤ 2.85 n^{2/3}`; `5.9 ≤ (n+1)g_n³`, `n g_n³ ≤ 8.4`, `1.8(n+1)^{−1/3} ≤ g_n = a_n − a_{n+1} ≤ 2.05 n^{−1/3}`; for `1 ≤ k < n`: `a_k − a_n ≥ 1.8(n−k)n^{−1/3}`, and for `2 ≤ k < n`: `≤ 2.05(n−k)k^{−1/3}`; `\|a_n − a_k\| ≥ 1.8\|n−k\|max(n,k)^{−1/3}` for all `n ≠ k ≥ 1` | `airyZero_cube_bounds`, `airyZero_abs_cube_bounds`, `airyZero_abs_bounds`, `airyZero_gap_between`, `airyZero_delta_bounds`, `airyZero_gap_cube_bounds`, `airyZero_gap_bounds`, `airyZero_separation`, `airyZero_separation_lower`, `airyZero_abs_sub_ge` (`AiryZeroSpacing`) | `(2/3)Δ/ρ_{n+1} ≤ ρ_{n+1}² − ρ_n² ≤ (2/3)Δ/ρ_n`, `Δ = ρ_{n+1}³ − ρ_n³ ∈ [4.56, 4.87]`; telescoping with `a_1 − a_2 > 1.65` for `k = 1`; mpmath: `g_n n^{1/3} ∈ [1.805, 1.871] → (2/3)(3π/2)^{2/3} = 1.8739`; constants not optimal |
| **Lemma Z (CFT survey) in explicit form**: `\|a_n + ((3π/2)(n−1/4))^{2/3}\| ≤ 0.1 n^{−4/3}` (`n ≥ 2`) | `airyMin_lemma`, `airyZero_delta_cube`, `airyZero_delta` (`AiryZeroLemmaZ`) | from the phase theorem; true `\|δ_n\|n^{4/3} = 0.0155 (n=2) → (5/48)(3π/2)^{−4/3} = 0.0132`; the second term `5/(48t²)` is proved in the next rows (`AiryZeroSecondOrder`) |
| **Saddle integral to `w^{-9}` (the `u₂` term)**: `‖∫ e^{-ws²-is³/3} ds − (π/w)^{1/2}(1 − 5/(48w³) + 385/(4608 w⁶))‖ ≤ (34459425/268738560)√(π/ρ)/ρ⁹` (`ρ = Re w > 0`); same for `Ai(w²)` with prefactor `e^{-(2/3)w³}/2π`; general Taylor remainder `‖e^{ix} − Σ_{m<n}(ix)^m/m!‖ ≤ \|x\|^n/n!` | `airySO_taylor_le`, `norm_saddleJ0_fourth_le`, `norm_airyAiC_sq_fourth_le` (`AiryZeroSecondOrderSaddle`) | proved; complex moments by integration by parts, real `∫s^{18}e^{-ρs²}` by `Γ(19/2)`; `385/4608·4/9 = u₂ = 385/10368` |
| **`χ = Ai + iBi` and `Ai`, `Bi` on the negative axis to `O(r^{-9})`** (`r = √y`, `φ = (2/3)r³ − π/4`, `a = 1 − 385/(4608 r⁶)`, `t = 5/(48 r³)`): `‖χ(−r²) − (√π√r)^{-1} e^{−iφ}(a + it)‖ ≤ (1/2)/(√r r⁹)`; `\|Ai(−r²) − (√π√r)^{-1}(a cos φ + t sin φ)\| ≤ (1/2)/(√r r⁹)`; `Bi` with `t cos φ − a sin φ` | `airySO_chi_neg_sq`, `airySO_Ai_neg_sq`, `airySO_Bi_neg_sq` (`AiryZeroSecondOrderChi`) | proved; DLMF 9.7.9/9.7.11 to `u₂`; true sup of `√r r⁹·err` is `u₃(3/2)³/√π = 0.0723` (mpmath); the imaginary part `t` of the amplitude is correct to `O(ξ^{-3})` since the `ξ^{-2}` term is real |
| **Zero phase to `O(ξ^{-3})` (DLMF 9.9.6/9.9.18, phase form)**, `n ≥ 2`, `r = √(−a_n)`: `\|(2/3)r³ − (n − 1/4)π − 5/(48 r³)\| ≤ (11/10) r^{-9}` | `airyZero_phase_second`, `airySO_phase_alg` (`AiryZeroSecondOrderPhase`) | proved from `airyZero_phase_r` + `airySO_Ai_neg_sq`; mpmath: `r⁹·(…) = −0.1098 (n=2) → −0.1199` |
| **DLMF 9.9.18 second order for the zeros, explicit constants** (`n ≥ 2`, `t = (3π/2)(n−1/4)`): `\|a_n + t^{2/3}(1 + 5/(48t²))\| ≤ 2 t^{-10/3} ≤ 2 n^{-10/3}`; **Lemma Z with its second term**: `\|a_n + t^{2/3} + (5/48)t^{-4/3}\| ≤ 2 t^{-10/3}`; `∃C ∀n ≥ 1`: `\|a_n + t_n^{2/3}\| ≤ C n^{-4/3}` and `\|a_n + t^{2/3}(1+5/(48t²))\| ≤ C t^{-10/3}` | `airySO_invert`, `airyZeroT`, `airyZero_second_order`, `airyZero_second_order_n`, `airyZero_delta_second`, `airyZero_delta_exists`, `airyZero_second_order_exists` (`AiryZeroSecondOrder`) | proved; no numerics in the proof; mpmath `t^{10/3}(a_n+T₂)` = 0.1004 (n=1) → 5/36 = 0.1389 (the next DLMF term `−(5/36)t^{-4}`), so the constant 2 is about 14 times the truth. Not formalised: the `−(5/36)t^{-4}` coefficient (needs `u₃`), the zeros of `Ai'` (DLMF 9.9.19), the `Tendsto` form of the sharp limit, sharper spacing as a corollary |
| **Prüfer angle of `Ai`**: `θ(a_n) = −(n−1)π` exactly (normalisation `0 < θ(0) < π`); for `y ≥ \|a_2\|`: `\|θ(−y) + (2/3)y^{3/2} − 3π/4\| ≤ π/2 + 0.14` (sawtooth, sharp amplitude `π/2`); `\|θ(−y) + ξ(y)\| ≤ 4.1`, `\|−θ(−y)/ξ(y) − 1\| ≤ 4.1/ξ(y)` | `airyPrufer_mono`, `airy_prufer_airyZero`, `airy_exists_airyAi'_zero`, `airyAi'_zero_location_r`, `airyAi'_zero_phase_of_gap`, `airyPrufer_corner`, `airy_prufer_deviation_bracket`, `exists_airyZero_bracket`, `airy_prufer_deviation`, `airy_prufer_ratio` (`AiryPruferAsym`) | `tan θ = Ai/Ai' ≈ y^{−1/2}cot φ`: `θ` is a staircase (plateaus at zeros of `Ai`, jumps `−π` at zeros of `Ai'`), not `π/2 − φ`; proof: on `[a_n,b_n]`, `[b_n,a_{n+1}]` `θ` lies between exact end values and `ξ` between located values (`a_n`: error `2/5 ρ^{−3}`; zeros `b_n` of `Ai'`: `\|φ−nπ\| ≤ (π/2)\|sin φ\| ≤ 1.12 r^{−3}`). mpmath (unwrapped `arg(Ai'+iAi)`): `sup \|D\| = 0.8808` on `4.0879 ≤ y ≤ 60`, increasing slowly to `π/2` |
| **Zeros of `Ai'`**: exactly one zero `b_n` in each gap `(a_{n+1}, a_n)`; `\|(a_n − b_n)/(a_n − a_{n+1}) − 1/2\| ≤ 0.4/n` (`n ≥ 2`) (Clark node `α = π/2`: midpoint) | `airyAi'_existsUnique_zero_gap`, `airyClark_sq_cube`, `airyMid_key_lower`, `airyMid_key_upper`, `airyMid_sigma_le`, `airyMid_lower_ratio`, `airyMid_upper_ratio`, `airyMid_core`, `airyAi'_zero_midpoint` (`AiryClarkMid`) | uniqueness: `Ai' = 0 ⇔ θ ∈ π/2 + πℤ`, one level in `(−nπ, −(n−1)π)`; fraction from the phases in the cubes and `(2/3)(t³−ρ³)/t ≤ t²−ρ² ≤ (2/3)(t³−ρ³)/ρ`; true value `1/2 + 0.0249…/n` (mpmath, n = 2…100) |
| **Airy shift identity**: for every solution of `y'' = xy` on `ℝ`, `y(X+s) = y(X) C(X,s) + y'(X) S(X,s)`, `y'(X+s) = y(X) C_s + y'(X) S_s`, `C, S` the solutions of `Y'' = (X+s)Y` with data `(1,0)`, `(0,1)`; P3 `lem:airy2-shift-parity`(i) (A:1068) | `airy_shift`, `airyAi_shift`, `airyAi'_shift`, `airyBi_shift`, `airyShiftC`, `airyShiftS`, `airyShiftCd`, `airyShiftSd`, `isSol_airyShiftC`, `isSol_airyShiftS`, `airyShift_initial`, `airyShift_det` (`AiryShift`) | `C = π(Bi'(X)Ai(X+s) − Ai'(X)Bi(X+s))`, `S = π(Ai(X)Bi(X+s) − Bi(X)Ai(X+s))` are *defined* through `Ai, Bi` and `W(Ai,Bi) = 1/π`; the identity is ODE uniqueness. `(Bi, Bi')` is a real solution, `isAirySol_airyBi_shift` (with `Bi' = airyBiDeriv` and the real Wronskian `airyWronskian_real` of `AiryBiReal`). Not formalised: power-series recurrence for `C, S` (only their Taylor expansion with remainder), parameter dependence of the paper's `C(s;ζ,h)` |
| P3 A:1121: `Ai(X+s)Bi(X) − Ai(X)Bi(X+s) = −S(X,s)/π` | `airyShift_wronskian_shift` (`AiryShift`) | by definition of `S`; the lower bound `\|S(s₊)\| ≥ c` needed in `lem:airy2-recessive`(ii) is not formalised |
| Taylor of a solution of `y'' = xy` to order 4 (derivative: 3) and 5 (4) with remainder bounded by the sup of the next jet: `y⁽⁵⁾ = 4xy + x²y'`, `y⁽⁶⁾ = (x³+4)y + 6xy'`; first terms `C = 1 + Xs²/2 + s³/6 + X²s⁴/24 + Xs⁵/30 + O(s⁶)`, `S = s + Xs³/6 + s⁴/12 + X²s⁵/120 + O(s⁶)` | `airyTaylor_chain`, `airyJetOf`, `airy_sol_taylor4`, `airy_sol_taylor5`, `airyShiftC_taylor`, `airyShiftS_taylor` (`AiryShiftTaylor`) | no `1/n!` gain in the remainder (`B\|s\|ⁿ`); hypothesis is a bound on the segment |
| **Taylor remainder of `Ai` against the weight** `airyWt X = (2+\|X\|)^{-1/4}e^{−(2/3)X₊^{3/2}}`: for `X ≥ −1`, `\|s\| ≤ 1`, `\|s\|√(1+\|X\|) ≤ Λ`: `\|Ai(X+s) − T₄\| ≤ K e^Λ\|s\|⁵(1+\|X\|)^{5/2}airyWt(X)`, `\|Ai'(X+s) − T₃'\| ≤ K e^Λ\|s\|⁴(1+\|X\|)^{5/2}airyWt(X)`; next order `\|s\|⁶(1+\|X\|)³`, `\|s\|⁵(1+\|X\|)³` (W1 `lem:ec-defect` Taylor step EC:78-86; P3 A:1068-1104 order bookkeeping) | `airy_taylor4`, `airy_taylor5`, `airy_envelope_ge_neg_two`, `airyJet5_bound`, `airyJet6_bound`, `airy_segment_geometry` (`AiryShiftTaylor`) | `K` existential; the hypothesis `\|s\|√(1+\|X\|) ≤ Λ` is necessary (the unrestricted bound fails like `e^{√X}`). `Ai(X+s)` is not controlled by `airyWt(X)` uniformly in `\|s\| ≤ 1` |
| **`airyWt`** (an explicit stand-in for the weight `M/E` of Olver, not equal to it): positivity; `airyWt/20 ≤ Ai ≤ 6 airyWt`, `\|Ai'\| ≤ 720√(2+\|X\|) airyWt` on `[−1,∞)`; local constancy `airyWt ξ ≤ (6/5)e^Λ airyWt X` for `\|ξ−X\| ≤ 1`, `\|ξ−X\|√(1+\|X\|) ≤ Λ` | `airyWt`, `airyWt_pos`, `airyWt_le_one`, `airyWt_sq_le`, `airyWt_div_twenty_le_airyAi`, `airyAi_le_six_airyWt`, `abs_airyAi'_le_airyWt`, `airyWt_le_of_close` (`AiryWt`) | constants far from sharp (true ratio range of `Ai/airyWt` on `[−1,60]`: `[0.284, 0.705]`); built on `airyAi_envelope_real`, `abs_airyAi'_le_mul_airyAi` |
| **lattice sums of `airyWt²`** (P3 A:1131-1133): `Σ_{i≤n} airyWt(X_i)² ≤ 2 + (2/g)(√(2+A)+√(2+B))` for a lattice in `[−A,B]` with spacings `≥ g`; scaled form `(2 + 4√(2+C₀)/c)δ^{-2}` for `g = cδ`, window `C₀δ^{-2}` | `airyWt_sq_lattice_sum`, `airyWt_sq_lattice_sum_scaled` (`AiryWt`) | only the lower spacing bound is used; `airyWt²` is not integrable at `−∞`, hence the window dependence |

### CFT consequences of the Airy zeros (`FormalResearch/Special/AiryCft*.lean`, namespace `FormalResearch.Special`)

Direct route by good circles for the CFT/modular-bootstrap notes (`SE5_FIVE_LEVEL_AIRY`, `FOLD_TIP_THEOREM`, `UPPER_TRANSFER`, `GENERAL_THEOREMS`, `AIRY_POISSON`): no general Hadamard theory is used (the Weierstrass/Hadamard product of `Ai` is `Hadamard.airyAiC_hadamard` in the section *Complex analysis: Hadamard factorization* below, proved independently). `a_n = airyZero n`, `n ≥ 1`. Mathlib has no residue theorem for poles; the generic factorisation/circle machinery (`AiryCftCircle`, `AiryCftResidue`) is Airy-free. **Not formalised:** the `Ai'/(P·Ai+Q·Ai')` good-circle estimate (GENERAL_THEOREMS Lemma 1.0′), Clark-Airy summation for `ψ_α` (Thm 1.1) and Theorem D for `P·Ai + Q·Ai'` (all need the derivative analogue of `AiryAsymNegComplex`), Theorem Q for `ν ∈ [−1, 1/2]` (Hardy unfolding, Fejér–Riesz), `f` holomorphic only near the closed disc, sharp constants (`45`, `30√π` against numerical `0.989`, `2.01`).

| Statement | Lean | Notes |
|---|---|---|
| **Generic circle machinery**: `CftCircleData f c s R` (`f` entire, its zeros in `\|w\| ≤ R` simple, listed by `c` over `s`); division `f = Π(w − c_i)·φ` with `φ` zero-free on the disc; circle formulas `F(z) − Σ1/(z−c_i)` and `F'(z) + Σ(z−c_i)^{-2}` as Cauchy integrals of `F = f'/f`, with error bounds | `CftCircleData`, `cftCircle_factor`, `cftCircle_logDeriv`, `cftCircle_deriv_logDeriv`, `cftCircle_error_one`, `cftCircle_error_two` (`AiryCftCircle`) | proved; generic complex analysis, no Airy |
| **Generic residue formula**: `f` entire with simple zeros `c_i` in `\|w\| < R`, `H` entire: `∮_{\|w\|=R} H/f = 2πi Σ H(c_i)/f'(c_i)` | `cftCircle_residue` (`AiryCftResidue`) | proved; factorisation `f = Π(w − c_i)φ` (Lagrange-type subtraction) plus Cauchy–Goursat |
| **Zeros of `Ai` in `ℂ`, simplicity, good circles as data**: `Ai(w) = 0 ↔ w = a_n (n ≥ 1)`; `Ai'(a_n) ≠ 0`; every `R` splits the list (`n ≤ N ↔ \|a_n\| < R`); `‖Ai'/Ai‖ ≤ 45√(1+r)` on a good circle | `airyAiC_eq_zero_iff`, `airyZero_deriv_ne_zero`, `airyZero_split`, `airy_circleData`, `airy_circleData_exists`, `airy_logDeriv_norm_le` (`AiryCftZeros`) | proved; the bound from (E1′) + (E2) (numerically sup `0.989`) |
| **Mittag-Leffler / logarithmic-derivative expansion** (SE5 `r(z) = r(0) + Σ(1/(z−a_n) + 1/a_n)`, UPPER_TRANSFER Lemma ID, GENERAL_THEOREMS): for `z ∈ ℂ`, `Ai(z) ≠ 0`: `Ai'(z)/Ai(z) = Ai'(0)/Ai(0) + Σ_{n≥1}(1/(z−a_n) + 1/a_n)` (`HasSum`, absolutely convergent); real form for real `x` | `airyAiC_logDeriv_mittagLeffler`, `airyAi_logDeriv_mittagLeffler_real`, `airyCft_summable_series` (`AiryCftMittagLeffler`) | proved, no Hadamard theory: on the good circles `\|w\| = r_k`, `Ai = Π_{\|a_n\|<r}(w−a_n)φ`, Cauchy's formula for `φ'/φ` gives remainder `(2πi)⁻¹∮F(ζ)z/(ζ(ζ−z))dζ = O(r^{-1/2})`; summability from `\|a_n\| ≥ 2.5 n^{2/3}`; mpmath-checked (tail `~N^{-1/3}`) |
| **Sum rule `(log Ai)'' = −Σ(x−a_n)^{-2}`** (FOLD_TIP_THEOREM Seed lemma): `Σ_{n≥1}(z−a_n)^{-2} = (Ai'(z)/Ai(z))² − z`, `Ai(z) ≠ 0` (via `F' = z − F²`); `Σ a_n^{-2} = (Ai'(0)/Ai(0))² = 3^{2/3}Γ(2/3)²/Γ(1/3)² = 0.53146`; at a zero `x` of `Ai'`: `Σ(x−a_n)^{-2} = −x` (so `S_1 = Σ(a_n−a_1')^{-2} = \|a_1'\|`) | `airyAiC_logDeriv_sq_series`, `airyAi_sq_series_real`, `airyZero_sum_inv_sq`, `airyZero_sum_inv_sq_closed`, `airyZero_sum_sq_of_deriv_zero`, `airyAi_ne_zero_of_deriv_zero` (`AiryCftMittagLeffler`, `AiryCftZeros`) | proved; second-order circle formula `cftCircle_deriv_logDeriv` (no termwise differentiation); `a_1'` is not constructed here, the identity holds at any zero of `Ai'` |
| **Theorem D (residue-defect formula)** (AIRY_POISSON §2) for entire `f`: `\|Σ_{n≤N} f(a_n)/Ai'(a_n)² − ∫_{−R}^R f\| ≤ πRM` on a good circle if `\|f R_±\| ≤ M` on the half circles (`R_± = (Bi ∓ iAi)/Ai`); `Bi(a_n) = −1/(πAi'(a_n))` | `airy_defect_bound`, `cftDef_residue`, `cftDef_airyBiC_at_zero` (`AiryCftDefect`) | proved for `f` entire (entire primitive via `Differentiable.isExactOn_univ`); the exact identity with `A_±` as integrals is an intermediate step, not a separate statement; mpmath 70 digits: identity to `10⁻⁵⁰`. Combined with `good_circle_ratio_bounds` for `M = 30√π·sup\|f\|/e` |
| **Corollary D1 (Airy quadrature)** (AIRY_POISSON D1; case `ν < −1` of Theorem Q): `f` entire, `‖f(u)‖ ≤ C(1+\|u\|)^ν e(u)` on `ℂ`, `ν < −1`: `∫_ℝ f = Σ_{n≥1} f(a_n)/Ai'(a_n)²` (absolutely convergent); `f ∈ L¹(ℝ)` automatically | `airy_quadrature`, `airy_integrable_real`, `airy_summable_weighted`, `airyZero_inv_deriv_sq_le`, `airyEnv_ofReal_neg`, `airyEnv_ofReal_le_one`, `airyCft_circles_ratio` (`AiryCftWeights`, `AiryCftQuadrature`) | proved; `1/Ai'(a_n)² ≤ 36π²(1+\|a_n\|)^{-1/2}`, `e = 1` on the negative axis; the sum converges iff `ν < −1`. Non-vacuity of the hypothesis class (smearings of `Ai`, slow `n^{-1/6}` tail) is numerical/mathematical only, not a Lean statement |

### Langer coordinate (`FormalResearch/Special/Langer*.lean`, namespace `FormalResearch.Special`)

Module M3 of the discrete-to-Airy plan: the turning-point coefficient lemma behind P3 `thm:general-rank-airy` (A:1152) and W1 `lem:ec-defect` (est:277-281). For a coefficient `F` (or rank-turn data `u`) with a simple turn, the Langer coordinate `ζ` with `ζ ζ'² = F` is `C^{m+1}`, with positive derivative and amplitude ratio. Hypothesis convention for the downstream steps: `m ≥ 1` always (`u ∈ C²` gives `ζ ∈ C²`; the jets need `u ∈ C³`). All proved, axioms `[propext, Classical.choice, Quot.sound]`. **Not formalised:** analyticity of `ζ`, `g` for analytic `u` (the route gives `C^k` for every finite `k`), the identification of `u` with `(E−b)/(2a)` for the specific chains, uniformity of the constants in the parameters `(E, h)`, the fourth Taylor coefficient `−1/35` of `Φ`, and everything about the discrete chain (parametrix defect, recessive solution, window: the next subsection).

| Statement | Lean | Notes |
|---|---|---|
| `Φ(z) = arcosh(1+z)²` (`-arccos(1+z)²` for `z<0`) is analytic at the turning point `0`; it is the inverse of the entire `∑_{n≥1} wⁿ/(2n)! = cosh√w - 1` | `analyticAt_langerPhi`, `langerP_langerPhi`, `langerPhi_langerP`, `analyticAt_langerP` (`LangerPhi`) | W1 est:279 "`arcosh(1+z)² = 2z + O(z²)`"; via Mathlib `analyticAt_comp_iff_of_deriv_ne_zero` |
| eikonal relation `cosh √Φ(z) = 1+z` (`z ≥ 0`), `cos √(-Φ(z)) = 1+z` (`-2 ≤ z < 0`) | `cosh_sqrt_langerPhi`, `cos_sqrt_neg_langerPhi` (`LangerPhi`) | P3 A:1152 "eikonal `cosh(ζ^{1/2}ζ') = τ u`" |
| `Φ'(0)=2`, `Φ''(0)=-2/3`, `Φ'''(0)=8/15` (series `2z - z²/3 + 4z³/45`) | `deriv_langerPhi_zero`, `deriv2_langerPhi_zero`, `deriv3_langerPhi_zero` (`LangerPhi`) | from `iteratedDeriv_langerCosh_zero`; next coefficient `-1/35` only checked in sympy |
| jets of `F = Φ(u-1)` at `u = 1`: `F' = 2u'`, `F'' = 2u'' - (2/3)u'²`, `F''' = 2u''' - 2u'u'' + (8/15)u'³` (Taylor coefficients `F₁ = 2u₁`, `F₂ = 2u₂ - u₁²/3`, `F₃ = 2u₃ - (2/3)u₁u₂ + (4/45)u₁³`) | `langerF_jets` (`LangerJets`) | P3 A:1152; `u ∈ C³` |
| Hadamard's lemma in `C^k`: `F ∈ C^{m+1}` at `c ⟹ dslope F c ∈ C^m` at `c`; `(F q - F c)/(q-c) = ∫₀¹ F'(c+t(q-c))dt` | `contDiffAt_dslope`, `contDiffOn_hadInt`, `hasDerivAt_hadInt`, `dslope_eq_hadInt` (`LangerHadamard`) | generic; dominated differentiation under the integral, induction on `m` |
| **Langer coordinate at a simple turn** (`F ∈ C^{m+1}`, `F c = 0`, `F' c > 0`, `m ≥ 1`): `ζ = langerZetaOf F c` is `C^{m+1}`, `ζ'(c) = (F' c)^{1/3}`, near `c`: `ζ' > 0`, `ζ ζ'² = F`, sign `ζ = sign(q-c)`, `ζ/(q-c)` is `C^m` and positive | `langerZetaOf_spec` (`LangerCoordinate`) | cube-root trick: `ζ = (q-c)a²`, `a = (3M/2)^{1/3}`, `M = ∫₀¹ √t √G(c+t(q-c))dt`, `G = F/(q-c)`; `ζ' = √G/a` |
| `ζ` is the paper's `±(3/2∫√\|F\|)^{2/3}`: `(2/3)ζ^{3/2} = ∫_c^q √F` (`q ≥ c`), `(2/3)(-ζ)^{3/2} = ∫_q^c √(-F)` (`q ≤ c`) | `langerZetaOf_integral`, `langerZeta_integral` (`LangerCoordinate`) | W1 est:277-278 `(2/3)ζ_E^{3/2} = ∫η`; FTC on `ζ^{3/2}` |
| rank-turn data `u ∈ C^{m+1}`, `u(q*) = 1`, `u'(q*) > 0`: `ζ = langerZeta u q*` is `C^{m+1}`, `ζ'(q*) = (2u'(q*))^{1/3}`, `ζ ζ'² = Φ(u-1)` | `langerZeta_spec` (`LangerCoordinate`) | P3 A:1152 (`F₁^{1/3}`), `cosh√F = u` |
| positive amplitude: `sinh²η = u²-1`; `ζ/(u²-1)` (`dslope` form) is `C^m`, positive, `= \|ζ\|/\|u²-1\|` for `q ≠ c`, value `(2u')^{-2/3}` at `c`; `g = (4\|ζ\|/\|D̄\|)^{1/4}`, `D̄ = 4a²(1-u²)`, is `C^m` and positive for a positive `C^m` coefficient `a` | `langerAmpRatio_spec`, `langerAmp_of_coeff` (`LangerCoordinate`) | W1 est:279-281 "`sinh²η/(t-t*)` is `C³` and positive"; here exactly `(u+1)·dslope u` |

### Discrete-to-Airy limit (parametrix, recessive solution, window, wiring, hard edge, actual chains) (`FormalResearch/Special/AiryParametrix*.lean`, `AiryRecessive*.lean`, `AiryWindow*.lean`, `DiscreteAiryLimit*.lean`, namespace `FormalResearch.Special`)

Modules M4-M7 and the wiring layer of the discrete-to-Airy plan, on top of the Airy side (`AiryWt`, `AiryShift*`), the Langer coordinate (`Langer*`) and the discrete Jacobi calculus (`DiscreteJacobi*`; `jac a c y k = a(k+1) y(k+1) + a k y(k-1) - c k y k`, `δ³ = h`). These modules are imported by `FormalResearch.Special`, not by the `Airy` aggregate. P3 `thm:general-rank-airy` and `lem:airy2-recessive` (A:1068-1160), W1 `lem:ec-defect`, `lem:recessive`, `eq:airyfactor` (est:255-382), with the Bi-type second solution replaced by the reduction-of-order solution `secondSol` (Casoratian 1). Every statement is a **proved under explicit hypothesis** theorem (axioms `[propext, Classical.choice, Quot.sound]`); the hypotheses are listed in the rows. The amplitude relation `g²Aζ'Sh(ζζ'²) = 1`, assumed by M4, is proved for M3's own `ζ, g` by M7a (`AiryParametrixLanger`); the `(1+|X|)³` factor of M4 is removed by M7b (`AiryParametrixUniform*`: uniform defect `≤ K h² airyWt X` for every real `X`, from the `h`-expansion of the shift functions at fixed `ζ`). The wiring layer (`DiscreteAiryLimit*`, rows at the end of the table) composes M1-M7 for a simple turn: for one fixed smooth shape it verifies `hdef`, `hdefW`, the junction data and `Sg`, `Qq` from Langer data plus an `O(h²)` comparison of the recurrence coefficients, and applies it to the closed-form Hahn / centred Racah coefficients of `Racah/P3JacobiComparison`. It covers the recessive solution with relative `O(h)` error and a bounded oscillatory window for one fixed `(u, A, c₀)` under the hypothesis (R) on the forbidden-end values; it is a counterpart of GBVA Thm 3.8 / Geronimo 2009 Thm 2.6 in that regime, not a replacement for them (the papers' cited input is still cited). Two further layers discharge (R) and identify the chains for the closed forms. *Hard edge* (`DiscreteAiryLimitHyper*`): monotone backward decay to the hard edge `A_{N+1} = 0` (`backward_ratio` with `exact_hyperbolicity_hahn_racah` row by row), so that (R) holds up to **one normalisation** `|Y_{k₁}| ≤ δ^{-p}` at an early forbidden-side site (the decay runs from `k₁` to the edge, so a bound at the end of the chain gives nothing at `k₁`). *Actual chains* (`DiscreteAiryLimitChains*`): for **integer data** the actual Wigner `3j`/`6j` natural-gauge chains `Ŷ_k = √(2k+1)Φ_k` satisfy the closed-form Hahn / centred Racah recurrence (the square-root gauge change of the paper's exact rank recurrences `Phi3j_rank_recurrence`, `Phi6_midpoint_recurrence`) with end conditions, `|Ŷ| ≤ √N` from one term of the Gauss weight, and the composition with the Airy limit, in which (R) is proved, not assumed. **Not formalised:** the normalisation `|Y_{k₁}| ≤ δ^{-p}` for the abstract closed-form chains (Darboux matching with `κ` identified, or orthogonality), half-integer chain data (the chain lives on the shifted lattice `k ∈ ℤ+½`; `jac`, `hrAk`, `hrCk` are `ℤ`-indexed), the existence of lattice nodes `x_n = x` (a congruence condition; `hahn_chain_airy` is for a fixed `x` and one example is `M = σ = 0`, `x = 1/2`, `N = 4t+2`, `n = 3t+1`) and uniformity of the constants over compact families, the Racah turn data (the derivation of `q_* = 2αβ sinθ/γ` and the branch `τ = -1`, the `(-1)^k` twist of `racah_class_chain`; `racah_chain_airy` takes `τ = +1` and the turn data as hypotheses), `Ŷ_{k_max} ≠ 0`, the sharper exponential decay `prop:forbidden-decay`(b),(c), the quantum-`6j` (`sinh/cosh`) variant of hyperbolicity, the Darboux/Wigner-`d` normalisation `κ` and `κ ≠ 0` (left existential; the parity factor and lattice quantisation), the non-recessive canonical `Ai`/`Bi` pair (`cos(πK)Ai - τ sin(πK)Bi`), the oscillatory side beyond a bounded window (Olver `M, E` on `X < -A0`), the second-order bracket, uniformity over compact families of shapes, the `q`-Racah chain, analyticity of `ζ` (`A ∈ C²`, `u ∈ C³` only), the `h²` coefficient of the defect, the sharper `(1+X⁺)^{-1/2}` saving in `f₂`, and sharp or tracked constants (all `K, C, δ₀` are existential; `windowConst` is `e^{O(A0²)}`, numerically very pessimistic).

| Statement | Lean | Notes |
|---|---|---|
| Airy shift Taylor error with explicit Lyapunov bounds for `C, S` (`Y'' = (X+s)Y`): `\|C\|, \|S\| ≤ e^Λ` for `\|s\|√(1+\|X\|) ≤ Λ`, `\|s\| ≤ 1`, and fifth-order remainders | `apx_CS_bounds`, `apx_C_taylor`, `apx_S_taylor` (`AiryParametrixShift`) | existential constants; used by the defect lemma; Taylor polynomials, parity and monotone bounds in `AiryParametrixPoly` (`apx_skel_A`, `apx_skel_B`), parity skeleton `sk_even_odd`, `sk_odd_even` (`AiryParametrixSkeleton`), `langerCosh_taylor` (`AiryParametrixTaylor`) |
| `Ai`, `Ai'` against the weight on all of `ℝ`: `\|Ai x\| ≤ 25 airyWt x`, `\|Ai' x\| ≤ 132500 √(2+\|x\|) airyWt x` | `apx_airy_global` (`AiryParametrixPointwise`) | non-optimal constants (Olver `M/E`, `N/E` on `x<-1`, `AiryWt` on `x ≥ -1`) |
| pointwise parametrix defect `\|G₊Ai(X+Δ₊)+G₋Ai(X+Δ₋)-2G₀Ch(F)Ai(X)\| ≤ K h²(1+\|X\|)³airyWt X`, from jet bounds and the transport identity | `apx_pointwise` (`AiryParametrixPointwise`), `apx_defect_core` (`AiryParametrixDefect`) | real-variable form, `h = t³`, `X = z₀/t²`; the odd orders cancel algebraically (eikonal `Ch(F) = u`, parity under `s → -s`) |
| `q`-derivative of the amplitude relation `g²Aζ'Sh(ζζ'²) = 1`: `2G₁ζ'Sh+G₀ζ''(Sh+2F Sh')+G₀ζ'⁴Sh' = 0`; uniform jets and Taylor remainders on a compact `J ⊆ U` | `apx_transport`, `apx_jet2`, `apx_jet3` (`AiryParametrixJets`) | `G₀ = Ag`, `G₁ = A'g/2+Ag'`, `Sh = 2 deriv langerCosh` |
| **Parametrix defect lemma, window form** (W1 est:255-382, P3 A:1068-1135; M4): `A, g ∈ C²(U)`, `ζ ∈ C³(U)`, `U` open, `J ⊆ U` compact, **assumed amplitude relation** `g²Aζ'Sh(ζζ'²) = 1` on `U`: `∃ K h₀`, `0<h≤h₀`, `q∈J`, `X = h^{-2/3}ζ(q)`: `\|A(q+h/2)ψ(q+h)+A(q-h/2)ψ(q-h)-2A Ch(ζζ'²)ψ(q)\| ≤ K h²(1+\|X\|)³ airyWt X`, `ψ = g·Ai(h^{-2/3}ζ)` | `airyParametrix_defect` (`AiryParametrixDefect`) | superseded for the turn neighbourhood by `airyParametrix_defect_uniform` below (the factor `(1+\|X\|)³` here is not small for `X ~ h^{-2/3}`; this window form is its weaker corollary); `Ch = langerCosh`; `ζζ'² = Φ(u-1)` gives `c = 2A u` (`cosh_sqrt_langerPhi`); `A > 0`, `ζ' > 0` not needed; the relation is discharged for M3's data by `langer_hrel` below |
| bounded window `\|X\| ≤ R`: defect `≤ K(1+R)³h²airyWt X` (contains the `h^{5/3}` stage) | `airyParametrix_defect_bounded` (`AiryParametrixLattice`) | same hypotheses, assumed amplitude relation (`hrel`; for M3's data see `langer_hrel`); the uniform form below has no `(1+R)³` |
| lattice form: `a k = A(q₀+kh-h/2)`, `c k = 2A(q_k)Ch(ζζ'²)(q_k)`, `ψ k = g(q_k)Ai(h^{-2/3}ζ(q_k))` ⟹ `\|jac a c ψ k\| ≤ K h²(1+\|X_k\|)³airyWt X_k` when `q_k ∈ J` | `airyParametrix_defect_lattice` (`AiryParametrixLattice`) | `jac = FormalResearch.DiscreteAiry.jac`; `K, h₀` independent of `q₀, k`; same assumed amplitude relation and `(1+\|X_k\|)³` factor; uniform form `airyParametrix_defect_uniform_lattice` below |
| `Ch(w)² - 1 = w Sh(w)²` for all real `w` (`Ch = cosh√w`, `Sh = 2Ch' = sinh√w/√w`, entire) | `langerCosh_sq_sub_one` (`AiryParametrixLanger`) | M7a; proved on `w>0` and extended by the identity theorem; `Sh(0)=1`, `Sh>0` near `0` (`langerSinhc_zero`, `langerSinhc_pos_nhds`) |
| **Amplitude relation for the Langer coordinate** (closes the M3/M4 gap): `u∈C³`, `u c=1`, `u'c>0`, `A∈C²`, `A c>0`: on an open `U∋c`, `ζ=langerZeta u c ∈ C³`, `A, g=langerAmp u A c ∈ C²`, `A,g,ζ'>0`, `g²Aζ'Sh(ζζ'²)=1` and `Ch(ζζ'²)=u` | `langer_hrel` (`AiryParametrixLanger`) | M7a; `g⁴ = 1/(A²ζ'²Sh²)` for `q≠c`, `q=c` by continuity; `U` local (not explicit), `A, u` hypotheses at the point `c` only |
| **Parametrix defect for M3's data (no assumed relation), window form and lattice form**: for every compact `J ⊆ U`, `\|jac a d ψ k\| ≤ K h²(1+\|X_k\|)³ airyWt X_k` on `q_k∈J`, `a k=A(q_k-h/2)`, `d k=2A(q_k)u(q_k)`, `ψ k=g(q_k)Ai(h^{-2/3}ζ(q_k))` | `airyParametrix_defect_langer_window`, `airyParametrix_defect_langer` (`AiryParametrixLanger`) | M7a; `airyParametrix_defect(_lattice)` with `hrel` discharged by `langer_hrel`, diagonal `2Au`; `d k` needed only at `q_k∈J`; `K, h₀` independent of `q₀, k`; still the `(1+\|X\|)³` factor (the uniform version is obtained by composing with `airyParametrix_defect_uniform_lattice`, not stated separately) |
| Confluent equation of `Ch = langerCosh`: `Ch(w) = 4w Ch''(w) + 2 Ch'(w)` and its first two derivatives | `apuc_ode0`, `apuc_ode1`, `apuc_ode2` (`AiryParametrixUniformCh`) | M7b; from `cosh(√w s)`, `cos(√(-w) s)`; `apuc k = Ch^{(k)}` |
| Closed-form `h`-coefficients of the shift functions `C(s;ζ,h)`, `S(s;ζ,h)` (`Y''=(ζ+hs)Y`): `E=Ch(ζs²)`, `O=s³(Ch'/2-Ch'')`, `A=2sCh'`, `B=s⁴Ch''`, with `E''=ζE`, `O''=ζO+sE`, `A'=E`, `B''=ζB+sA` | `apu_hasDerivAt_E1`, `apu_hasDerivAt_O1`, `apu_hasDerivAt_A`, `apu_hasDerivAt_B1` (`AiryParametrixUniformCh`) | M7b; parity and compact bounds `apu_bounds`, `apuc_bound` |
| Energy Gronwall for `R''=qR+f`, `R(0)=R'(0)=0`: `\|R\| ≤ φ(S+1)e^{(2+L)S}` on `\|x\| ≤ S`, both signs of `x` | `apu_gron` (`AiryParametrixUniformODE`) | M7b |
| Shift functions at fixed `ζ`: `\|C(ζ/t²,ts)-(E+hO)\| ≤ Kh²`, `\|S(ζ/t²,ts)/t-(A+hB)\| ≤ Kh²`, uniform in `\|ζ\| ≤ Z0`, `\|s\| ≤ S`, `0<t≤1`, `h=t³`, no `X`-dependence | `apu_C_remainder`, `apu_S_remainder` (`AiryParametrixUniformODE`) | M7b; P3 A:1068-1104 at order `h¹` with `h²` remainder |
| Pointwise uniform defect: `\|G₊Ai(X+Δ₊)+G₋Ai(X+Δ₋)-2G₀Ch(F)Ai(X)\| ≤ Kh²airyWt X` (real data, transport identity) | `apu_pointwise` (`AiryParametrixUniformPointwise`) | M7b; replaces `apx_pointwise` (no `(1+\|X\|)³`); core `apx_defect_core_uniform` (`AiryParametrixUniformDefect`) |
| **Uniform parametrix defect lemma** (W1 est:255-382, P3 A:1068-1135): `A, g ∈ C²(U)`, `ζ ∈ C³(U)`, `U` open, `J ⊆ U` compact, **assumed** `hrel` `g²Aζ'Sh(ζζ'²)=1` on `U`: `∃ K h₀`, `0<h≤h₀`, `q∈J`, for **every** real `X = h^{-2/3}ζ(q)`: `\|A(q+h/2)ψ(q+h)+A(q-h/2)ψ(q-h)-2A Ch(ζζ'²)ψ(q)\| ≤ K h² airyWt X` | `airyParametrix_defect_uniform` (`AiryParametrixUniformDefect`) | M7b; no factor `(1+\|X\|)³`, turn neighbourhood `X ~ h^{-2/3}` and oscillatory side included; `hrel` holds for M3's data by `langer_hrel`; constants existential |
| uniform lattice form: `\|jac a c ψ k\| ≤ K h² airyWt X_k` for `q_k ∈ J` | `airyParametrix_defect_uniform_lattice` (`AiryParametrixUniformLattice`) | M7b; same lattice hypotheses as `airyParametrix_defect_lattice`; `K, h₀` independent of `q₀, k` |
| relative form: `\|jac a c ψ k\| ≤ K h² \|ψ k\|` when `q_k ∈ J`, `X_k ≥ -1` | `airyParametrix_defect_uniform_rel` (`AiryParametrixUniformLattice`) | M7b; from `Ai ≥ airyWt/20` and `g² ≥ 1/(1+sup\|Aζ'Sh\|)` (from `hrel`), no sign hypothesis on `g`; supplies M5's `hdef` (`C₀ = K`) when `g > 0` on `J`; not available for `X_k < -1` (`ψ` has zeros) |
| **Recessive solution, kernel bound** (P3 `lem:airy2-recessive`(i), A:1105-1124): relative defect `\|jac ψ\| ≤ C₀h²ψ` (`hdef`), `ψ ≍ airyWt` on a lattice window (`AiryLattice`: `X ≥ -1`, `X ≤ Bh^{-2/3}`, spacings `≥ c₁h^{1/3}`; `AiryComparison`: `κ₁ airyWt ≤ ψ ≤ κ₂ airyWt`), `a ≥ c_a`: `Σ_{i>k}\|K_{ki}\| ≤ Qh` and the flux sums `≤ Φδ⁵` | `volterraK_row_sum_le`, `flux_bound_le`, `kernel_term_le`, `expTail_le`, `expTail_sum_le` (`AiryRecessiveKernel`, `AiryRecessiveSums`) | no `Bi`, no Olver `M/E`: `airyWt_le_exp_mul` replaces `ψ_i ≤ Ce^{-(ξ_i-ξ_j)}ψ_j`; `hdef` is a hypothesis; only the lower spacing bound is used; `Q` is far above the numerical value (`‖K‖/h ≈ 3·10⁻³`) |
| **`lem:airy2-recessive`(i)**: the exact solution `f` with `f = ψ` at the last two sites has `\|f-ψ\| ≤ Cδ³ψ`, `ψ/2 ≤ f ≤ 3ψ/2`, and `\|(f-ψ)_k-(f-ψ)_{k+1}\| ≤ Cδ⁵ψ_k+Cδ³\|ψ_k-ψ_{k+1}\|`; abstract version from row sums `≤ 1/4` | `recessive_airy`, `recessive_abstract`, `flux_formula` (`AiryRecessive`) | existence from `exists_final_solution_hom`, bound from `reduction_of_order_bound`; under `hdef`, `AiryLattice`, `AiryComparison`; the Lipschitz estimate is the input of the window lemma |
| **Recessive selection and second solution** (A:1155-1160, `lem:airy2-recessive`(ii) with `W = 1`; W1 `lem:recessive`): `Y = κf + μf₂`, `f₂ = secondSol`, `cas ≡ 1`, `μ = a_{N+1}(f_NY_{N+1}-f_{N+1}Y_N)`, `\|μ\| ≤ 3κ₂a_{N+1}Y_max e^{-ξ(X_N)}`, `0 ≤ f₂ ≤ C₂δ^{-1}/airyWt` | `physical_decomposition`, `abs_mu_le`, `abs_mu_le_airy`, `secondSol_le`, `secondSol_ge`, `recessive_selection_airy`, `recessive_airy_selection` (`AiryRecessiveSelection`) | same hypotheses as `recessive_airy`; `f₂` is the reduction-of-order solution (no `Bi`), Casoratian 1 replaces `\|𝒲\| ≥ ch^{1/3}`; `recessive_selection_airy` needs the ξ-gap condition (the gap must exceed `log(1/δ)+O(1)`) and the monotone decay `\|Y_{k₁}\| ≤ \|Y_{k₀}\|` as hypotheses; only `X ≥ -1` |
| lattice count of the oscillatory window, `(m-J)c₁δ ≤ X_m - X_J`; continuation of an exact solution below the top window by the recurrence | `window_count`, `window_len`, `extend_below` (`AiryWindow`, `AiryWindowMain`) | Airy-free; `extend_below` needs `a ≠ 0`, same values on `Icc m (N+1)` |
| homogeneous / inhomogeneous Grönwall march through the window, from the top two sites | `window_hom_bound`, `window_from_top`, `windowExp`, `windowConst` (`AiryWindow`) | wrap `jacobi_difference_bound_down`, `jacobi_solutions_bound_down`; constant `e^{O(A0²)}` with `Sg ≈ A0`; needs the near-hyperbolic coefficients as hypotheses |
| near-hyperbolic constants of the window from smooth coefficient data: `Sg = L_F C_z A + C_a`, `Qq = L_a C_s` | `window_hyperbolic_constants` (`AiryWindowMain`) | hypotheses: `\|c-a_k-a_{k+1}\| ≤ L_F\|s-s*\|+C_aδ⁶`, `\|s-s*\| ≤ C_zδ²A` (Langer), `a` Lipschitz in `s`, `s`-spacing `≤ C_sδ³`; abstract, not verified for any chain |
| **Discrete-to-Airy comparison on a bounded window `X ≥ -A0`** (P3 `thm:general-rank-airy`(i) column form; W1 `eq:airyfactor` on bounded windows; up to `κ`): exact solution `f` of the rows `Icc (J+1) N`, `f = ψ` at `N, N+1`, `\|f-ψ\| ≤ Cδ³ψ` on `Icc m (N+1)` (`X ≥ -1`), `\|f-ψ\| ≤ Cδ³W` on `Icc J m` (`X ∈ [-A0, Z]`) | `discrete_airy_window` (`AiryWindowMain`) | **hypotheses:** `δ ≤ δ₀` (asymptotic regime, `δ₀` existential); `AiryLattice`, `AiryComparison` on the top window; lower spacing `≥ c₁δ` and `X_m - X_J ≤ S` on the window; `a ≥ c_a`; near-hyperbolic `\|c-a_k-a_{k+1}\| ≤ Sg δ²`, `\|a_{k+1}-a_k\| ≤ Qq δ²` on `Ioc J m` (`Sg`, `Qq`); relative defect `hdef` on `Icc (m+1) N` and **absolute** defect `hdefW` `\|jac ψ\| ≤ C₀δ⁶W` on `Ioc J m` with `W ≥ ψ_m` (no positivity of `ψ` there); junction `ψ_m ≤ W`, `\|ψ_m-ψ_{m+1}\| ≤ Λδ W`; `hdef` on `X ≥ -1` is supplied by `airyParametrix_defect_uniform_rel` (for `g > 0`, `hrel` from `langer_hrel`; `C₀ = K`), while the absolute `hdefW` on `X < -1` is the weight form `airyParametrix_defect_uniform_lattice` (`K h² airyWt`), wired to the closed-form Hahn/Racah coefficients by `discrete_airy_limit` below; `C = windowConst`, pessimistic `e^{O(A0²)}` (numerically the error is `≈ 0.016 h^{4/3}`); `κ` not determined |
| same for the physical solution `Y = κf + μf₂`: `\|Y-κψ\| ≤ Cδ³\|κ\|W + (2/(c_aw₀))windowExp·\|μ\|/δ` on `Icc J m`, `\|Y-κψ\| ≤ Cδ³\|κ\|ψ + secondConst·\|μ\|/δ/airyWt` on `Icc m (N+1)` | `discrete_airy_window_physical` (`AiryWindowMain`) | all hypotheses of `discrete_airy_window` plus `w₀ ≤ ψ_m`, `Y` solving the rows `Icc (J+1) N`, `\|Y_N\|, \|Y_{N+1}\| ≤ Y_max`; `\|μ\| ≤ 3κ₂a_{N+1}Y_max e^{-ξ(X_N)}`; `κ, μ` existential |
| Taylor remainders of `Ai`, `Ai'` on `X ∈ [-A0, -1]`, `\|s\| ≤ 1` (orders 4/3 and 5/4) with constants polynomial in `A0` | `airy_taylor4_window`, `airy_taylor5_window`, `airy_window_bounds` (`AiryWindowTaylor`) | complements `airy_taylor4`, `airy_taylor5` (`X ≥ -1`, `AiryShiftTaylor`) for the base-point Taylor step |
| **Smooth data of a simple turn on a closed window** (wiring layer): `u ∈ C³`, `u(c₀)=1`, `u'(c₀)>0`, `A ∈ C²`, `A(c₀)>0`, any `r₀>0`: `r ≤ r₀`, open `U ⊇ [c₀-r,c₀+r]`, `ζ=langerZeta u c₀ ∈ C³(U)`, `A, g=langerAmp ∈ C²(U)`, `g²Aζ'Sh(ζζ'²)=1`, `Ch(ζζ'²)=u`, `0<c₁≤ζ'≤c₂`, `0<g_min≤g≤g_max`, `0<A_min≤A≤A_max`, Lipschitz constants of `A, g, u` | `dal_turn_data`, `DalTurnWin` (`DiscreteAiryLimitData`) | compactness + mean value; constants existential |
| **Lattice window indices**: `ζ ∈ C¹`, `ζ(c₀)=0`, `0<c₁≤ζ'≤c₂`: for `δ ≤ δ₀` and every `q₀` there are indices `J ≤ m ≤ N` with `q_J ≥ c₀-A₀δ²/c₂`, `q_J < c₀-A₀δ²/c₂+δ³` (so `X_J ≤ -(c₁/c₂)A₀+c₁δ`), `c₀ ≤ q_m < c₀+δ³`, `c₀+r/4 ≤ q_N`, `q_{N+1} ≤ c₀+r/2`, spacings `c₁δ ≤ X_{k+1}-X_k ≤ c₂δ`, `X_k = h^{-2/3}ζ(q_k)`, `h = δ³` | `dal_lattice_window`, `dal_lattice_window_struct`, `DalLat` (`DiscreteAiryLimitLattice`, `DiscreteAiryLimitDefect`) | ceilings/floors and the mean value inequality for the spacings |
| **Exact-coefficient defect on the window**: `\|jac a⁰ c⁰ ψ\| ≤ Kδ⁶ airyWt X` (all `X`) and `≤ K'δ⁶ψ` on `X ≥ -1`, `a⁰_k=A(q_k-h/2)`, `c⁰_k=2A(q_k)u(q_k)` | `dal_exact_defect` (`DiscreteAiryLimitDefect`) | M7b lattice and relative forms with `langer_hrel` (eikonal `Ch(ζζ'²)=u`) |
| **All hypotheses of the window theorems for perturbed coefficients** (`AiryLattice`, `AiryComparison`, spacing, near-hyperbolic `Sg, Qq`, relative defect on `X ≥ 0`, absolute defect on `X ∈ [-A₀,0]`, junction, `w₀ ≤ ψ_m`) for `a, c` with `\|a_k-A(q_k-h/2)\| ≤ Eh²`, `\|c_k-2A(q_k)u(q_k)\| ≤ Eh²` | `dal_window_hyp`, `AiryWindowHyp`, `dal_f_lat` and the other `dal_f_*` field lemmas (`DiscreteAiryLimitSetup`, `…Fields`, `…Hyp`) | explicit constants (`κ₁=g_min/20`, `κ₂=6g_max`, `W=25g_max`, `c_a=A_min/2`, …); `E` enters `C₀, Sg, Qq`; this is the paper's `A_k=a₀(s)+O(h²)`; proved under the stated hypotheses |
| **Discrete-to-Airy limit at a simple turn, abstract form** (P3 `thm:general-rank-airy`(i), W1 `eq:airyfactor`): for `δ ≤ δ₀` and every `q₀` the window positions are exported (`q_J ∈ [c₀-Dδ²,c₀]`, `c₀ ≤ q_m < c₀+δ³`, `c₀+r/4 ≤ q_N`, `q_{N+1} ≤ c₀+r/2`, `X_J ≲ -A₀`); the exact recessive solution `f` of the rows with `f = ψ` at `N, N+1` has `\|f-ψ\| ≤ Cδ³ψ` (`X ≥ 0`) and `≤ Cδ³W` (`X ∈ [-A₀,0]`); every exact solution `Y` with `\|Y_N\|, \|Y_{N+1}\| ≤ Y_max` is `κf + μf₂`, `\|μ\| ≤ C_μ Y_max e^{-ξ₀/δ³}`, `\|Y-κψ\| ≤ Cδ³\|κ\|W + C_osc\|μ\|/δ` (window), `≤ Cδ³\|κ\|ψ + C_top\|μ\|/(δ airyWt)` (top) | `discrete_airy_limit`, `DalConclusion` (`DiscreteAiryLimit`) | **proved** for the data of `dal_turn_data` (`u'(c₀)>0`, `A(c₀)>0`, `\|a-A(·-h/2)\|, \|c-2Au\| ≤ Eh²`). Counterpart of GBVA Thm 3.8 / Geronimo 2009 Thm 2.6 for the recessive solution and a bounded oscillatory window only: no non-recessive `Ai`/`Bi` pair, no oscillatory side beyond the window, no uniformity over families; `κ` produced by the recessive selection, not identified (no Darboux matching), `κ ≠ 0` not proved; constants existential, window constant `e^{O(A₀²)}`; numerics: relative error `≈ 0.025h` (model chain), `≈ 0.27h` (Hahn closed forms), numerical evidence only |
| **Bounded-window form**: for `\|Y_N\|, \|Y_{N+1}\| ≤ δ^{-p}` (hypothesis (R)), every `n`, `Z`, `δ ≤ δ₁(n,p,Z,…)`: `∃ κ`, `\|Y_k-κψ_k\| ≤ Cδ³\|κ\|W + δⁿ` on `[J, N+1] ∩ {X ≤ Z}` (so `Y = κ g (Ai + O(h))` when `\|κ\| ≥ δ^s`, `n > 3+s`) | `dal_conclusion_window`, `dal_exp_small`, `dal_airyWt_ge_Z` (`DiscreteAiryLimitWindow`) | proved; (R) is a hypothesis on the forbidden-end values, not derived from the `3j/6j` orthogonality |
| **Hahn / centred Racah closed forms are a simple turn**: `A(q)=½ẽ(q²)`, `u(q)=τ(x-β₀q²)/ẽ(q²)` are `C^n` at `q_*`, `A(q_*)>0`, `u(q_*)=1`, and `u'(q_*)>0` from `1-τx>0` (AM-GM identity `σ(Pβ+Qα-2τβ₀s) ≥ 2s(1-τx)`) | `hrA_contDiffAt`, `hrA_pos`, `hrU_contDiffAt`, `hrU_turn`, `hr_alg`, `hrU_deriv_pos` (`DiscreteAiryLimitHahnTurn`) | proved; hypotheses of `prop:exact-hyperbolicity` (`Φ(q_*²)=0`, `τ²=1`, `1-τx>0`) plus strict interior `Pq_*²<1`, `Qq_*²<1`, `q_*>0`, `P,Q ≥ 0`; no convexity of `Φ` used |
| **Closed-form coefficients are `O(h²)`-perturbations**: `A_k=½r_kẽ((kh)²)`, `c_k=τ(x-B_k)` (`hrAk`, `hrCk`) satisfy `\|A_k-A(q_k-h/2)\| ≤ 2(a²+b²+⅓)/q_*²·h²` and `\|c_k-2A(q_k)u(q_k)\| ≤ ρ₂h²` for `k ≥ q_*/(2h)`, `q_k=(k+½)h` | `hr_coef_A`, `hr_coef_C`, `hr_perturb`, `hrE`, `hrAk`, `hrCk` (`DiscreteAiryLimitHahn`) | proved from `rr_sub_one_le`, `Bk_close` (`Racah/P3JacobiComparison`) |
| **Discrete-to-Airy limit for the closed-form Hahn / centred Racah recurrence** (P3 `thm:hahnAiryConnection`, `thm:racahAiryConnection`, up to the listed obligations): with `q_k=(k+½)δ³`, exports `1 ≤ J ≤ m ≤ N`, `q_*-Dδ² ≤ q_J ≤ q_*`, `q_* ≤ q_m < q_*+δ³`, `X_J ≤ -A₀`, then `DalConclusion` for every solution of `jac (hrAk …) (hrCk …) Y = 0` (window form: same positions with the bounded-window bound) | `discrete_airy_hahn_racah`, `discrete_airy_hahn_racah_window` (`DiscreteAiryLimitHahn`, `DiscreteAiryLimitWindow`) | proved under the P3 simple-turn hypotheses; `τ=-1` is the `(-1)^k`-twist of the natural gauge. Here (R) is a hypothesis and `Y` is any solution of the closed-form recurrence; (R) is derived from the hard edge up to one normalisation in `discrete_airy_hahn_racah_hardedge(_window)` and proved for the actual integer-data chains in `hahn_chain_airy`, `racah_chain_airy` (rows below). Not covered: `κ` unidentified and `κ ≠ 0` unproved, no non-recessive `Ai`/`Bi` pair, no oscillatory side beyond the bounded window, no uniformity over families of `x`, `(a,b)`; not a full GBVA/Geronimo replacement |
| **Backward monotone decay to the hard edge.** `A_i>0` on `[j,N]`, `A_{N+1}=0`, `A_i+A_{i+1} ≤ c_i`, rows `A_{i+1}Y_{i+1}+A_iY_{i-1}=c_iY_i` on `[j,N]`: `\|Y_k\| ≤ \|Y_{j-1}\|` for `j-1 ≤ k ≤ N` (including `Y_N=0`) | `hd_backward_decay`, `hd_zero_backward` (`DiscreteAiryLimitHyperDecay`) | proved; P3 `prop:forbidden-decay`(a); `backward_ratio` with `y=1` plus zero propagation |
| **Hard-edge decay for the closed-form Hahn / centred Racah chains.** Rows of `jac (hrAk…)(hrCk…)` on `[k₁+1,k_max]`, hard edge `ẽ(((k_max+1)h)²)=0`, `(k₁+½)h ≥ q*`, `2Mh ≤ q*`, `h(ρ₁+ρ₂) ≤ 2κq*`: `\|Y_k\| ≤ \|Y_{k₁}\|`, `k₁ ≤ k ≤ k_max`; `A_i>0` on the chain | `hr_hardedge_decay`, `hr_Ak_pos`, `hrRho` (`DiscreteAiryLimitHyperDecay`) | proved; `exact_hyperbolicity_hahn_racah` row by row (gap `q_k-q* ≥ h ≥ C₀h²`); closed forms, not by itself the actual `3j/6j` chains; mpmath check in the docstring (numerical evidence only) |
| **Discrete-to-Airy limit for the closed-form chains with (R) replaced by hard-edge data.** Window position, `DalConclusion`, and for `Y` on `[J+1,k_max]` with the hard edge and `m ≤ k₁ ≤ N`: `N+1 ≤ k_max`, `\|Y_k\| ≤ \|Y_{k₁}\|` on `[k₁,k_max]`; bounded-window form: `\|Y_{k₁}\| ≤ δ^{-p}` gives `\|Y_N\|,\|Y_{N+1}\| ≤ δ^{-p}` and `∃κ`, `\|Y_k-κψ_k\| ≤ Cδ³\|κ\|W+δⁿ` on `[J,N+1] ∩ {X ≤ Z}` | `discrete_airy_hahn_racah_hardedge`, `discrete_airy_hahn_racah_hardedge_window`, `hr_edge_beyond` (`DiscreteAiryLimitHyperWindow`) | proved; (R) is derived from the single normalisation `\|Y_{k₁}\| ≤ δ^{-p}`, which is not derived (Darboux / orthogonality); `κ` unidentified |
| **`prop:hahn-class`, integer case: the actual `3j` chain is the closed-form Hahn Jacobi chain.** For integers `M, σ`, `N > 0`, rational `x = 2μ/N`, `Ŷ_k = √(2k+1) Φ_k^{M,σ}(x;1/N)` satisfies `A_{k+1}Ŷ_{k+1} + A_kŶ_{k-1} = (x - Mσ/(k(k+1)))Ŷ_k` for every `k ≥ 1`, `A_k = ½ r_k ẽ((kh)²)`, `h = 1/N` (`hrAk 1 0`, `hrCk 1 0 1`): exactly the data of `discrete_airy_hahn_racah` with `P=1, Q=0, τ=1` | `hahn_class_chain`, `hahn3jY` (`DiscreteAiryLimitChains3j`); helpers `chain_extend_rows`, `natgauge_row`, `hrAk_eq`, `hrB_hahn` (`DiscreteAiryLimitChainsCore`) | proved; from `Phi3j_rank_recurrence` (DLMF 34.3.15) by the square-root gauge change and the zero extension at the end rows. Integer case only (half-integer `L` is on the other sublattice, not translated) |
| **Hahn chain: support and end conditions.** `Ŷ_k = 0` unless `max(\|M\|,\|σ\|) ≤ k ≤ N-1`; `A_{k_max+1} = A_N = 0` (the hard edge) and `A_{k_min} = 0` for `k_min = max(\|M\|,\|σ\|) ≥ 1` | `hahn_chain_support`, `hahn_end_upper`, `hahn_end_lower`, `hrAk_lower_zero` (`DiscreteAiryLimitChainsCore`) | proved; `A_{k_max+1}=0` is the `hend` hypothesis of `backward_ratio`; `Ŷ_{k_max} ≠ 0` not proved |
| **`prop:racah-class`, integer case: the actual `6j` chain is the closed-form centred Racah Jacobi chain.** For integers `a,b,c,m,n`, `A = wA a n > 0`, `B = wB b m > 0`, any `h > 0`, `x = cosA A B (c+½)`, `P = 1/(4(Ah)²)`, `Q = 1/(4(Bh)²)`: `Ŷ_k = √(2k+1)Φ_k` satisfies `jac (hrAk P Q m n h) (hrCk P Q 1 x m n h) Ŷ k = 0` for every `k ≥ 1`; `A_k = R_kη_k/(k√(4k²-1))`, `B_k = (2k(k+1)+1-m²-n²)/(8AB) + mn/(k(k+1))` (`eq:racahAkexact`, `eq:racahBkexact`) | `racah_class_chain`, `racah6jY` (`DiscreteAiryLimitChains6j`); `hrB_racah` (`DiscreteAiryLimitChainsCore`) | proved; from `Phi6_midpoint_recurrence` (DLMF 34.5.11); `h` is a free scale (`h²β₀ = 1/(4AB)`); all chambers; branch `τ = +1` only (the `(-1)^k` twist is not written) |
| **Racah chain: support and end conditions.** `Ŷ_k = 0` unless `max(\|m\|,\|n\|) ≤ k ≤ min(2b+m, 2a+n)`; `A_{k_max+1} = 0` since `k_max+1 = min(2B,2A)`; `A_{k_min}=0` for `k_min = max(\|m\|,\|n\|) ≥ 1` | `racah_chain_support`, `racah_end_upper`, `racah_end_lower` (`DiscreteAiryLimitChains6j`) | proved |
| **`(R)` for the actual `3j` / `6j` chains** (`thm:general-rank-airy`(ii), T:889-892, T:1578-1585): at every lattice node of an admissible integer `3j` system `Ŷ_k² ≤ N`; at every physical `c_i` of a finite Racah system `Ŷ_f² ≤ 4AB/(2C)`; all `k ∈ ℤ` | `hahn_chain_sq_le`, `hahn_chain_abs_le`, `specAdm_int`; `racah_chain_sq_le`, `racah_chain_abs_le` | proved; one term of the Gauss-weight sum `gaussWeight_3j` / `gaussWeight_6j`; `3j` for `x = xLat M σ N n`, `n < N - max(\|M\|,\|σ\|)` |
| **Airy limit for the actual `3j` chain at the lattice nodes** (P3 `thm:hahnAiryConnection`, `thm:general-rank-airy`(i) for Hahn): fixed integers `M,σ`, rational `x ∈ (0,1)`, `A₀>0`: for every `N > max(\|M\|,\|σ\|)` with node `x_n = x`, `N⁻¹ ≤ δ₀³`, `δ = N^{-1/3}`: window positions as in `discrete_airy_hahn_racah` (`q_*=√(1-x²)`) and `κ, μ` with `\|μ\| ≤ C_μ√N e^{-ξ}`, `\|Ŷ_k - κψ_k\| ≤ Cδ³\|κ\|W + C_osc\|μ\|/δ` on `[J,m]`, `≤ Cδ³\|κ\|ψ_k + C_top\|μ\|/(δ airyWt X_k)` on `[m,N_w+1]` | `hahn_chain_airy` (`DiscreteAiryLimitChainsHahnAiry`) | proved: `discrete_airy_hahn_racah` ∘ `hahn_class_chain` ∘ `hahn_chain_abs_le`; (R) is proved here, not assumed; constants depend on `M,σ,x,A₀`; the existence of infinitely many nodes is a congruence condition that is not stated (example `M = σ = 0`, `x = 1/2`, `N = 4t+2`, `n = 3t+1`); `κ` unidentified, `κ ≠ 0` unproved |
| **Airy limit for the actual `6j` chain at the physical `c`-lattice** (P3 `thm:racahAiryConnection`): shape data `α,β>0`, `x`, `q_*` with the simple-turn hypotheses of `discrete_airy_hahn_racah` for `P=1/(4α²)`, `Q=1/(4β²)`, `τ=1`; for every finite Racah system, physical `c`, scale `h=δ³ ≤ δ₀³` with `Ah=α`, `Bh=β`, `cosA A B C = x`: same conclusion with `Y_max = √(4AB/(2C))` | `racah_chain_airy` (`DiscreteAiryLimitChainsRacahAiry`) | proved; integer data, `τ = +1` only; the turn hypotheses are taken as hypotheses (the derivation of `q_* = 2αβ sinθ/γ`, `Φ(q_*²) = 0` on the branch `(αx-β)(βx-α) ≤ 0`, and the `τ = -1` branch are not formalised) |

## Complex analysis: Hadamard factorization (`FormalResearch/Complex/Hadamard*.lean`, aggregate `FormalResearch.Complex`, namespace `FormalResearch.Hadamard`)

The Hadamard factorization theorem for entire functions of finite order, and its application to `Ai`. Mathlib has Jensen's formula, Borel–Carathéodory and the canonical decomposition of an entire function, but no Hadamard factorization, so this is upstreamable in principle. Only `HadamardAiry` imports Airy modules; no Airy module imports this aggregate. All headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`). **Not formalised:** the converse (a canonical product of finite genus has finite order), order = convergence exponent, lower bounds on canonical products on circles (replaced by a derivative route), orders and genera as defined notions (`hadamard` takes any `p` with `σ < p+1` and the exact growth form `C exp(C\|z\|^σ)`; no `limsup` definition), the closed value `Ai'(0)/Ai(0) = −3^{1/3}Γ(2/3)/Γ(1/3)` inside the product form (the theorem states `airyAi' 0 / airyAi 0`; the value is in `AiryValues`), `Σ 1/a_n` (conditionally convergent), the products of `Ai'` and `Bi`, Hadamard for meromorphic quotients.

| Statement | Lean | Notes |
|---|---|---|
| Weierstrass elementary factors `E_p(w) = (1−w)exp(w + … + w^p/p)`, `\|E_p(w) − 1\| ≤ e^p\|w\|^{p+1}` for `\|w\| ≤ 1`; for `Σ\|a_i\|^{-(p+1)} < ∞` the product `Π E_p(z/a_i)` converges locally uniformly, is entire, vanishes exactly on `{a_i}`, and has logarithmic derivative `Σ (z/a_i)^p/(z−a_i)` | `Hadamard.E_sub_one_le`, `Hadamard.hasProd_E`, `Hadamard.differentiable_canonProd`, `Hadamard.canonProd_ne_zero`, `Hadamard.canonProd_eq_zero`, `Hadamard.logDeriv_canonProd` (`HadamardProduct`) | proved; generic index type (`CanonData p a`); Weierstrass 1876 |
| Order of vanishing of the canonical product at `w` equals `#{i : a i = w}` | `Hadamard.analyticOrderNatAt_canonProd`, `Hadamard.CanonData.finite_fibre` (`HadamardProductOrder`) | proved |
| Multiplicity listing of the non-zero zeros of an entire `f ≢ 0` | `Hadamard.exists_listing`, `Hadamard.Listing` (`HadamardListing`) | proved |
| Convergence exponent (Jensen + dyadic blocks): `\|f(z)\| ≤ C exp(C\|z\|^σ)` implies `Σ\|a_i\|^{-s} < ∞` for `s > σ` | `Hadamard.Listing.ncard_le_mul_rpow`, `Hadamard.Listing.summable_rpow`, `Hadamard.Listing.canonData`, `Hadamard.GrowthBound` (`HadamardCount`) | proved; via Mathlib's `AnalyticOnNhd.sum_divisor_le` |
| Core estimate: `\|(f'/f − Σ_{\|a_i\|<R}(w/a_i)^p/(w−a_i))^{(p)}(z)\| ≤ K/R^{p+1}` on `\|z\| < R/4`, tending to `0` along good radii | `Hadamard.core_estimate` (`HadamardCore`), `Hadamard.core_bound_le` (`HadamardRadii`) | proved; finite Blaschke decomposition + Borel–Carathéodory (`HadamardBlaschke`) + Cauchy bounds (`HadamardCauchy`) |
| The `p`-th derivative of `f'/f − Σ_i (z/a_i)^p/(z−a_i)` vanishes on `{f ≠ 0}`, so the defect is a polynomial of degree `< p` | `Hadamard.iteratedDeriv_defect_eq_zero` (`HadamardDefect`) | proved; the derivative route replaces lower bounds on circles |
| **Hadamard factorization** (`f` entire, `‖f(z)‖ ≤ C exp(C\|z\|^σ)`, `0 < σ < p+1`): `Σ\|a_i\|^{-(p+1)} < ∞` and `f(z) = c z^m e^{P(z)} Π E_p(z/a_i)`, `c ≠ 0`, `deg P ≤ p`, `P(0) = 0`; the case `f 0 ≠ 0` has `c = f 0` | `Hadamard.hadamard`, `Hadamard.hadamard_floor` (`p = ⌊σ⌋`), `Hadamard.hadamard_exists` (`HadamardGeneral`), `Hadamard.hadamard_of_ne_zero` (`HadamardMain`) | proved; Hadamard 1893, Boas Thm 2.7.1, Titchmarsh 8.24, Conway VII.5.1; integer and non-integer order, zero at `0` allowed, any index type via `Listing` |
| **Hadamard product of `Ai`** (order `3/2`, genus `1`): `Σ\|a_n\|^{-2} < ∞` and `Ai(z) = Ai(0) exp((Ai'(0)/Ai(0))z) Π_n (1 − z/a_n) e^{z/a_n}`, `a_n` the zeros `airyZero (n+1)`, product locally uniformly convergent (UPPER_TRANSFER Lemma ID product form, SE5) | `Hadamard.airyAiC_hadamard`, `Hadamard.airy_listing`, `Hadamard.airyAiC_growth` (`HadamardAiry`) | proved; `p = 1`; the exponent is identified by differentiating at `0`. Its logarithmic derivative is the Mittag-Leffler row of the subsection *CFT consequences of the Airy zeros*, proved independently |

## Sturm/Prüfer theory for `y'' = x y` (`FormalResearch/Special/SturmAiry*.lean`, `AiryPrufer*.lean`)

Source: survey item WP4a (Prüfer angle, Sturm interlacing, Clark nodes in the CFT "Airy space" work; DLMF 9.9 for the zero structure). Everything is stated for arbitrary *real* solutions `(y, y')` of `y'' = q y` on `ℝ` (`SturmAiry.IsSol q y y'`: `HasDerivAt y (y' x) x`, `HasDerivAt y' (q x * y x) x`) with `q` continuous or, where stated, nothing; `q x = x` is the Airy equation. The Sturm layer itself uses no Airy function (`Ai` is connected through `AiryBridge`: `isSol_airyAi`), so the results apply to `Ai`, `Bi`, and `cos α · Ai - sin α · Ai'` (the last only in the sense of `IsSol.exists_unique_zero_*_combo`, it is not itself a solution). Namespace `FormalResearch.Special.SturmAiry`; all proved, axioms `[propext, Classical.choice, Quot.sound]`. Not formalised: solutions on a proper subinterval, the complex (Herglotz) Riccati equation, the sign of `u_α'` at zeros and the zero count of `u_α` for non-negative `q`. The `Ai`-specific values, the asymptotics of the zeros and of the Prüfer angle are built on this layer in the Airy section (`AiryZero*`, `AiryPruferAsym`, `AiryClarkMid`).

| Statement | Lean | Notes |
|---|---|---|
| uniqueness: `y a = y' a = 0 ⟹ y ≡ 0`; nontrivial ⟹ `(y x, y' x) ≠ 0` for all `x`; Wronskian constant; `wr = 0 ⟹ w = c y` | `IsSol.eq_zero_of_zero_data`, `IsSol.data_ne_zero`, `IsSol.wr_eq`, `IsSol.eq_smul_of_wr_eq_zero` (`SturmAiryZeros`) | Grönwall on `y² + y'²`, `q` continuous |
| zeros of a nontrivial solution are simple, isolated, finitely many on each `[a, b]` | `IsSol.deriv_ne_zero_of_zero`, `IsSol.eventually_ne_of_zero`, `IsSol.finite_zeros_Icc` (`SturmAiryZeros`) | |
| **Sturm separation**: between consecutive zeros `x₁ < x₂` of `y` exactly one zero of every `w` with `wr(y, w) ≠ 0`; at least one between any two zeros | `IsSol.sturm_separation`, `IsSol.exists_zero_of_wr_ne_zero`, generic form `exists_unique_zero_of_sep` (`SturmAiryZeros`) | Rolle on `f/g`; the generic form needs only `f' g - f g' ≠ 0` |
| `(w/y)' = wr/y²`; real Riccati `(y'/y)' = q - (y'/y)²` where `y ≠ 0` | `IsSol.hasDerivAt_div`, `IsSol.hasDerivAt_logDeriv` (`SturmAiryZeros`) | real only |
| **Sturm comparison**: `s'' = p s`, consecutive zeros `a < b`, `q ≤ p` on `[a, b]` ⟹ every solution of `y'' = q y` has a zero in `[a, b]` | `IsSol.exists_zero_Icc_of_comparison`, `IsSol.exists_zero_Icc_of_le_neg_one` (`SturmAiryComparison`) | zero in the closed interval (equality `y = s` possible); `p` continuous |
| `y'' = x y`: infinitely many zeros in `(-∞, 0]`; at most one zero in `[0, ∞)` for a nontrivial solution; `q > 0` on `(x₁, x₂)` and `y x₁ = y x₂ = 0` ⟹ `y ≡ 0` | `IsSol.infinite_zeros_of_le_neg_one`, `IsSol.infinite_zeros_Iic_zero`, `IsSol.zeros_Ici_zero_subsingleton`, `IsSol.eq_zero_of_two_zeros_of_pos` (`SturmAiryComparison`) | positive side from `(y y')' = y'² + q y² ≥ 0` |
| **Prüfer angle**: a nontrivial solution has a `C¹` lift `θ : ℝ → ℝ`, `y = r sin θ`, `y' = r cos θ`, `r > 0`, `θ' = cos² θ - q sin² θ` (`q x = x`: `θ' = cos² θ - x sin² θ`), normalised `θ t₀ = arg (y' t₀ + i y t₀)`; `θ' = 1` at zeros of `y` | `IsPruferLift`, `IsSol.exists_isPruferLift`, `IsPruferLift.zero_iff`, `IsPruferLift.hasDerivAt_eq_one_of_zero`, `IsPruferLift.contDiff_one` (`AiryPruferLift`) | `w = y' + i y`, `w = w(t₀) exp ∫ w'/w`; no Picard–Lindelöf; uniqueness of the lift mod `2π` is the next row |
| zeros are crossed exactly once, upward: each level `θ = kπ` attained at most once; `⌊θ/π⌋` nondecreasing; **count** `#{x ∈ (a, b] : y x = 0} = ⌊θ b/π⌋ - ⌊θ a/π⌋` (finite) | `crossing_forward`, `crossing_backward`, `eq_of_zero_of_zero`, `IsPruferLift.level_unique`, `IsPruferLift.floor_mono`, `IsPruferLift.zeros_ncard`, `IsPruferLift.zeros_finite` (`AiryPruferZeros`) | fencing theorem for `θ - kπ` |
| where `q ≤ -1` on `[a, b]`: `θ b - θ a ≥ b - a` and more than `(b-a)/π - 1` zeros in `(a, b]`; Airy: more than `(T-1)/π - 1` zeros in `(-T, -1]` | `IsPruferLift.sub_ge_of_le_neg_one`, `IsPruferLift.zeros_ncard_gt`, `airy_zeros_ncard_gt` (`AiryPruferZeros`) | lower bound only (no asymptotics) |
| interlacing of zeros of `cos α · y - sin α · y'` (`sin α ≠ 0`) and of `y` on `{q < 0}` (for `q x = x`: the negative axis), both directions, exactly one in between | `combo`, `IsSol.exists_unique_zero_combo_between`, `IsSol.exists_unique_zero_between_combo` (`SturmAiryInterlace`) | generalised Wronskian `∓ sin α (y'² - q y²)`; fails for `q > 0` |
| **Uniqueness of the Prüfer lift mod `2π`**: two lifts of the same `(y, y')` differ by a constant `2πk`; conversely `θ + 2πk` is a lift | `IsPruferLift.exists_int_eq_add`, `IsPruferLift.add_int_mul_two_pi` (`SturmAiryPruferUnique`) | pointwise difference in `2πℤ` (polar data of a nonzero vector), continuity + IVT ⟹ constant |
| **Polar form of `u_α`**: `cos α · y - sin α · y' = r sin (θ - α)`, `r > 0`; zeros of `u_α` are exactly `{x : θ x ∈ α + πℤ}` (iff); `u_α` is `C¹` (it is not a solution) | `IsPruferLift.combo_eq`, `IsPruferLift.combo_eq_zero_iff`, `IsSol.contDiff_combo` (`SturmAiryPruferUnique`) | convention `y = r sin θ`, `y' = r cos θ` as in `IsPruferLift` |
| **Zeros of `u_α` are simple** where `cos² α ≠ q(x₀) sin² α`, in particular where `q(x₀) < 0`: `u_α x₀ = 0 ⟹ u_α' x₀ ≠ 0` | `IsSol.deriv_combo_ne_zero_of_zero`, `IsSol.deriv_combo_ne_zero_of_zero_of_neg`, `IsSol.cos_sq_sub_pos` (`SturmAiryPruferUnique`) | at a zero `sin α · u_α' = (cos² α - q sin² α) y`, `cos α · u_α' = (cos² α - q sin² α) y'`; no sign of `u_α'` stated |
| `θ' > 0` where `q < 0`: `θ` strictly increasing on a convex `D` with `q < 0` on `interior D`; **zero count of `u_α`** `#{x ∈ (a, b] : u_α x = 0} = ⌊(θ b - α)/π⌋ - ⌊(θ a - α)/π⌋` (finite) for `q < 0` on `(a, b)` | `IsPruferLift.strictMonoOn_of_neg`, `IsPruferLift.combo_zeros_ncard`, `IsPruferLift.combo_zeros_finite`, generic `Levels.ncard_levels`, `Levels.finite_levels` (`SturmAiryNodes`, `SturmAiryLevels`) | `Levels` lemmas are pure real analysis for a strictly increasing `g`; general-`q` (zeros crossed upward only) version not formalised |
| **Interlacing, counting form**: `a < b` consecutive zeros of `u_α`, `q < 0` on `(a, b)`, `θ b = θ a + π`; for every `α'` exactly one zero of `u_α'` in `(a, b]`, in `(a, b)` if `sin (α' - α) ≠ 0`; with `α = 0` (`u_0 = y`) this reproves `exists_unique_zero_combo_between` (hypothesis on the open interval only); order `z_m^α < z_m^α' < z_{m+1}^α` for `α < α' < α + π` | `IsPruferLift.consecutive_combo_zeros_gap`, `IsPruferLift.exists_unique_combo_zero_between_combo_zeros`, `..._Ioo`, `IsSol.exists_unique_combo_zero_between_combo_zeros`, `IsSol.exists_unique_combo_zero_between_zeros`, `IsPruferLift.between_combo_zeros`, `Levels.level_succ`, `Levels.exists_unique_window`, `Levels.exists_unique_window_Ioo` (`SturmAiryNodes`, `SturmAiryLevels`) | a window of one period contains exactly one point of any lattice `c + πℤ` |
| **Position of the `m`-th node of `u_α` relative to the zeros of `y`**: for `jπ < α < (j+1)π`, `θ x = kπ`, `θ x' = α + mπ`: `x < x' ↔ k ≤ m + j`, and the node lies strictly between the `y`-zeros at levels `(m+j)π`, `(m+j+1)π`; on `(-∞, b]` (`q < 0` on `(-∞, b)`, `θ` unbounded below) each level `L ≤ θ b` is attained exactly once, so the zeros of `u_α` in `(-∞, b]` are `x_m`, `θ x_m = α + mπ`, `m ≤ ⌊(θ b - α)/π⌋`; `q x = x`, `b ≤ 0`: automatic | `Levels.lt_iff_of_levels`, `IsPruferLift.node_between`, `IsPruferLift.exists_unique_le_level`, `IsPruferLift.exists_unique_combo_zero_Iic_level`, `IsPruferLift.exists_floor_of_combo_zero`, `IsPruferLift.exists_le_of_le_neg_one`, `airy_exists_unique_combo_zero_Iic_level` (`SturmAiryNodes`) | generic in `θ`; the value of `θ b` for `y = Ai` (hence the index of the first node against the largest zero of `Ai`) is not part of this layer |

Airy-specific consequences (`AiryNodes.lean`): `airy_exists_prufer` (a `C¹` Prüfer lift of `(Ai, Ai')` with `θ 0 ∈ (π/2, π)`, strictly increasing on `(-∞, 0]`), `airy_zero_iff_level` (`Ai x = 0 ↔ θ x ∈ πℤ`), `airy_zeros_ncard` (`#{zeros of Ai in (a, 0]} = -⌊θ(a)/π⌋` when `0 < θ 0 < π`; the largest zero `a₁` is at the level `θ = 0`) and `airy_node_exists_unique` (the Clark nodes: for `α + mπ ≤ θ 0` exactly one zero `x ≤ 0` of `cos α·Ai − sin α·Ai'` at the level `α + mπ`). Not formalised here: node counts on `x > 0` (where `θ` stays in `(π/2, π)`). The asymptotics of `θ(-v)` (`airy_prufer_deviation`, `airy_prufer_ratio`), the ordered zeros `a_k` and their locations, and the Clark node `α = π/2` are in the Airy section (`AiryPruferAsym`, `AiryZeroOrder`, `AiryZeroLabel`, `AiryClarkMid`); the asymptotics of the general Clark nodes are not formalised.

### Discrete Jacobi calculus (`FormalResearch/Special/DiscreteJacobiCalculus*.lean`, `DiscreteJacobiExtras*.lean`)

Airy-free infrastructure for the discrete-to-Airy limit (P3 `thm:general-rank-airy`, `lem:airy2-recessive`, `prop:airy2-exact` (A:1105-1135); W1 `lem:recessive` est:291, `lem:ec-olver` EC:95). Exact identities with explicit constants; no asymptotics (the Grönwall rows give bounds, with the near-hyperbolic structure as hypothesis). Not formalised: the Airy-specific inputs live in the subsection *Discrete-to-Airy limit* (`AiryParametrix*`, `AiryRecessive*`, `AiryWindow*`); no growth of `Bi`; verification of the Grönwall hypotheses for the Hahn/Racah/W1 coefficients, the sharp Grönwall form `Σ ε_i exp(Lδ(n−i))`. Hard-edge conventions: the ordinary final-value window of a hard-edge chain (`a (N+1) = 0`) is the reduced window `Icc j (N−1)` (`hardEdge_window`), because the Casoratian across the bond `(N, N+1)` vanishes. All headline theorems depend only on `[propext, Classical.choice, Quot.sound]`.

| Statement | Lean | Notes |
|---|---|---|
| Lagrange identity / constant Casoratian of two solutions | `cas_sub`, `cas_eq_of_sol` (`DiscreteJacobiCalculus`) | `cas = a (k+1)(f k g (k+1) - f (k+1) g k)`; the paper's `𝒲` (A:1130) is `-cas a f1 f2` |
| uniqueness from two adjacent / final values | `eq_zero_of_two_values`, `eq_of_final_values` | `a ≠ 0` on the window |
| final-value Green function (`prop:airy2-exact`, A:1130) | `green_final`, `abs_greenFinal_le` | `e = Σ_{i>k} (f1 k f2 i - f2 k f1 i) r i / W`, `jac e = r`, `e N = e (N+1) = 0` |
| exact second solution by reduction of order, `cas = 1` | `secondSol`, `cas_secondSol`, `jac_secondSol`, `green_final_secondSol` | needs `f1` zero-free; replaces the Bi-type solution on the recessive side |
| reduction of order identity `D k - D (k-1) = -ψ jacψ (1+σ)` (A:1114-1118) | `reduction_identity` (`DiscreteJacobiCalculusVolterra`) | holds for any `y = ψ(1+σ)`, with the extra term `ψ k jac y k` |
| final-value Volterra form `σ k = -Σ K k i (1+σ i)` (A:1119) | `volterraK`, `volterra_final` | `K k i = jacψ i Σ_{j∈[k,i)} ψ i/(a(j+1)ψ_jψ_{j+1})` |
| sup-norm contraction; `|y-ψ| ≤ q/(1-q)|ψ|` if `Σ|K| ≤ q<1` (abstract `lem:airy2-recessive`(i)) | `contraction_sup`, `reduction_of_order_bound` | |
| solution = `κ f1 + μ f2` | `exists_combination` (`DiscreteJacobiCalculusComparison`) | |
| recessive selection (abstract W1 `lem:recessive`, est:291) | `recessive_selection_general`, `recessive_selection`, `recessive_selection_three`, `kappa_ne_zero` | `|μ| ≤ |κ||f1/f2|(k0)` for growth factor 3 |
| Z-matrix minimum principle / comparison (W1 `lem:ec-olver`(ii), EC:95) | `zmatrix_min_principle`, `zmatrix_comparison` | strict supersolution `zop w>0`; relation to `Racah.P3.backward_ratio` in the docstring |
| final-value problem has a solution (backward recursion), needs `a ≠ 0` on `Icc lo N` only | `exists_final_solution`, `exists_final_solution_hom`, `existsUnique_final_solution` (`DiscreteJacobiExtras`) | Airy-free; with `eq_of_final_values` gives existence+uniqueness; `exists_exact_near`: `f = ψ` at the last two sites, `f - ψ` solves `jac e = -jac ψ` |
| hard-edge backward ratio for ℤ-sequences, ℕ→ℤ extension | `backward_ratio_int`, `natExt`, `hardEdge_toInt`, `hardEdge_window` (`DiscreteJacobiExtrasHardEdge`) | glue to `Racah.P3.backward_ratio`; reduced window `Icc j (N-1)` |
| `\|y\|` non-increasing from exact hyperbolicity; supplies `hmono` of `recessive_selection` | `hardEdge_abs_antitone`, `hardEdge_abs_le_pow`, `recessive_selection_hardEdge`, `recessive_selection_hardEdge_nat`, `kappa_ne_zero_hardEdge` | A:1160 selection step abstractly; Airy inputs (`f1`, `f2`, λ=3) not included |
| scaled two-vector discrete Grönwall for `y_{k+1}=p y_k+q y_{k-1}+s` | `step_bound`, `three_term_bound` (`DiscreteJacobiExtrasGronwall`) | wraps Mathlib `discrete_gronwall`; state `(y,(y_k-y_{k-1})/δ)`, ℓ¹ size |
| bounded-window difference bound for `jac a c d = r` (up and down) | `jacobi_difference_bound`, `jacobi_difference_bound_down`, `jacobi_solutions_bound`, `jacobi_solutions_bound_down` | needs the near-hyperbolic structure; applied in `discrete_airy_window` (`AiryWindowMain`) |

## Weyl W1 free-fermion entanglement: exact finite algebra (`FormalResearch/FreeFermion`; reasoner `master` PRs #88, #91, #94)

Source: QIprojects `Weyl/free_fermion/paper/` (`parts/model.tex`, `parts/constants.tex`, `parts/resonance.tex`); aggregate `FormalResearch.FreeFermion`.
Only the exact finite algebra is formalised (no asymptotics, no Fock space). Headline theorems depend only on `[propext, Classical.choice, Quot.sound]` (pinned by `#print axioms`). All of it is on `master` (merged in PRs #88, #91 and #94).

| paper label | Lean | claim as formalised / caveats |
|---|---|---|
| `thm:heun` (Heun commutant of a Leonard pair; P1 `thm:Heun` is the folded-Racah specialisation) | `W1Heun.heun_commutant` (one side: `heun_side`; eigenvector lemma `W1Tridiagonal.eq_zero_of_eigen_of_tridiag`; entries `heun_diagonal_apply`, `sum_eq_iff`) | `X`, `Y` with eigenbases `e`, `f` (strictly increasing real eigenvalues), each irreducible tridiagonal in the other basis; `W`, `P` the spectral projections (`W e_n = [n ≤ K] e_n`); `H = {X-μ_X, Y-μ_Y}` with the midgaps. Then `H W = W H`, `H P = P H`; the matrices of `H` in `e`, `f` are tridiagonal with links vanishing exactly at the cut and nonzero elsewhere (Jacobi blocks); each of `Ran W`, `Ran(1-W)`, `Ran P`, `Ran(1-P)` carries a restriction of `H` with all eigenspaces of dimension at most one (simple spectrum). Caveats: more general than the paper (any bases over any `RCLike` field; self-adjointness and orthonormality are not used); finite index set is any finite linear order with adjacency `⋖`; spectral projections are characterised by their action on the eigenbasis rather than built by functional calculus |
| `prop:finite` (finite projector dictionary), all but `eq:replica` | `W1ProjectorDictionary.projector_dictionary` (parts: `spectrum_nonzero_eq`, `charpoly_mul_mul_eq`, `finrank_eigenspace_eq`, `hasEigenvalue_iff`, `adjoint_mul_self`, `commutator_eq`, `trace_variance`) | for orthogonal projection matrices `W`, `P`: nonzero spectra of `WPW`, `PWP` agree (indeed equal characteristic polynomials); eigenvalues of `C = WPW` and `K = (1-W)(1-P)(1-W)` outside `{0,1}` agree with multiplicity, using only `W² = W`, `P² = P` (`K A = A C`); `Aᴴ A = C(1-C)`; `Tr C(1-C) = ‖A‖_F² = ½‖[P,W]‖_F²`; `[P,W] = A - Aᴴ`. `C`, `K` are operators on the whole space, not compressions. **Not formalised:** the Fock-space half of `eq:replica` (`Tr(ρⁿ e^{iθN_A}) = det[(1-C)ⁿ + e^{iθ}Cⁿ]`, needs Fock space and Slater determinants); its linear-algebra half is the next row |
| `prop:res-twolevel`(c), (e) (exact `2×2` reduction, only the finite algebra) | `W1TwoLevel.twolevel_weight`, `twolevel_logit`, `twolevel_symmetric` | for `[[a,t],[t,d]]`, `t ≠ 0`, eigenvector of the lower (upper) eigenvalue: `p²/(p²+q²) = ½(1 ∓ Δ/√(Δ²+4t²))`; logit `2 arsinh(Δ/(2|t|))`; `Δ = 0` gives `1/2`. **Not formalised:** the reduction of the chain to `h(E)` and all `O(e^{-cL})` statements, `thm:res-doublet` |
| `prop:finite`, `eq:replica` (determinant half only) | `W1Replica.replica_det_eq_prod` (`replica_det_eq_prod_exp`, general `det_aeval_hermitian`, factors `replica_factor_zero`, `replica_factor_one`) | for a Hermitian complex matrix `C` with eigenvalues `c_k`, every `n`, `z : ℂ` (in particular `z = e^{iθ}`): `det[(1-C)ⁿ + z Cⁿ] = ∏_k ((1-c_k)ⁿ + z c_kⁿ)`; eigenvalues `0`, `1` give the factors `1`, `z` (`n ≥ 1`). **Not formalised:** that this equals `Tr(ρ_Aⁿ e^{iθN_A})` for a Gaussian state (the Fock-space/trace side); `Z_{n,L}(θ)` is not defined in Lean |
| `prop:bisp`(i) (Krawtchouk chain is a Leonard pair, Heun commutant exact) | `W1Krawtchouk.krawtchouk_heun` (`krawChain`, `krawX`, `krawY`, `krawBasis`; spectrum `krawY_hasEigenvalue_iff`; duality `krawX_matrix`; irreducibility `krawX_irreducible`, `krawChain_irreducible`; polynomial core `kL_kG`, `X_mul_derivative_kG`) | for every `N ≥ 1`, `0 < p < 1`, the paper's chain `a_n = √(pq(n+1)(N-n))/N`, `b_n = (p(N-n)+qn)/N` has spectrum exactly `{k/N}`; with `X = diag(n/N)` and `Y` the chain, `X` is irreducible tridiagonal in the eigenbasis `f_k` of `Y` (explicit matrix: diagonal `(kq+(N-k)p)/N`, links `√(pq)(N-k)/N`, `√(pq)k/N`) and `Y` in the standard basis, so `heun_commutant` applies: `H = {X-μ_X, Y-μ_Y}` commutes with both spectral projections at any cuts, with simple-spectrum Jacobi blocks. The duality is proved from the generating polynomials `(rt+s)^k(st-r)^{N-k}` (no Krawtchouk theory needed). **Not formalised:** orthogonality of `f`, the travel-time operator, `[T,P] = O(e^{-cN})`, the global-class margin (O) |
| `prop:bisp`, `eq:bispD`, `eq:bispF` (exact algebra), `cor:bispracah` | `W1Bispectral.krawtchouk_Dmu_factor`, `krawtchouk_orbit_endpoints`, `hahn_Dmu_factor`, `bispProfile_*`, `bisp_scale_algebra`, `bispracah_scale`, `bispracah_scale_explicit` | Krawtchouk `D_μ = 4pq t(1-t) - (μ-p-(q-p)t)² = (t-t_-)(t_+-t)`, `t_± = B(μ) ± 2√(pqμ(1-μ))`, `0 ≤ t_- ≤ t_+ ≤ 1` (`x = t`, `κ = 1`); Hahn limit symbols `4t²(1-t)² - (μ-2t(1-t))² = 4μ(t-t_-)(t_+-t)`; the profile `x = ½(x_++x_-) - ½(x_+-x_-)cos πτ` satisfies `x'² = π²(x-x_-)(x_+-x)`, `x(0) = x_-`, `x(1) = x_+`; `4 sinφ sin πτ_c/(π δ_c) = 8 sinφ (x_c-x_-)(x_+-x_c)/((x_+-x_-)Δx)` given `π sin(πτ_c)δ_c = 2Δx/(x_+-x_-)`, `sin²πτ_c = 4(x_c-x_-)(x_+-x_c)/(x_+-x_-)²`; the Racah specialisation `2Lα Δ sinφ/(1-β²) = 4Lαβ Δ^{3/2}/((1-α²)(1-β²))`. **Not formalised:** the global class, `T`, `δ_c`, `F` themselves, the ODE-uniqueness step `ω = π`, Hahn asymptotics (`A_N = t(1-t)+O(1/N)`), `T = Heun + O(L^{-1})` (the Hahn Leonard-pair duality is the next rows) |
| `prop:bisp`(ii) (Hahn chain `a_n = √(B(n)D(n+1))/N²`, `b_n = (B(n)+D(n))/N²`, `α, β > -1`, is a Leonard pair; sentence after `thm:heun`: "Krawtchouk, Hahn and dual Hahn chains are such pairs") | `W1Hahn.hahn_heun` (`hahnChain`, `hahnX`, `hahnY`, `hahnBasis`; spectrum `hahn_hasEigenvalue` (`W1HahnSpectrum`), `hahnY_hasEigenvalue_iff`; strict monotonicity `hahnEig_strictMono`; duality `hahn_dual_irreducible`; relation `hahn_tdRel`; chain irreducible `hahnChain_irreducible`) | for **all real `α, β > -1` and `N ≥ 1`** the spectrum is exactly `{k(k+α+β+1)/N²}`; with `X = diag(n/N)` and `Y` the chain, `X` is irreducible tridiagonal in an eigenbasis `f` of `Y` and `Y` in the standard basis, so `heun_commutant` applies (`H = {X-μ_X, Y-μ_Y}` commutes with both spectral projections at any cuts, simple-spectrum Jacobi blocks). The duality is proved from the tridiagonal relation `[Y₀,[Y₀,X₀]] - 2{Y₀,X₀} - (α+β)(α+β+2)X₀ = -(2N+β-α)Y₀ - N(α²+αβ+α+β)` (unscaled `Y₀ = N²Y`, `X₀ = NX`; `hahn_tdRel`) and the factorisation `(θ_i-θ_j)²-2(θ_i+θ_j)-(s²-1) = ((i-j)²-1)((i+j+s)²-1)`, `θ_k = k(k+s)`, `s = α+β+1` (`hahn_theta_factor`, nonzero for `|i-j| ≥ 2` when `s > -1`, a sufficient condition, sharp at `s = -1`); the spectrum from `Y P = P T` with `P_{kj} = r_k φ_j(k)`, `φ_j` falling factorials, `T` bidiagonal (`hahn_poly_id`, `hahn_chain_mul_P`). No Hahn polynomial theory; eigenvectors chosen not constructed. Generic machinery: `W1LeonardDual` (`tridiag_dual_of_relation`, `irreducible_of_tridiag_dual`, `exists_eigenbasis`, `hasEigenvalue_of_conj_upperTriangular`), `W1TridiagRelation` (`tdRel_triChain`, `triChain`). **Nomenclature:** the chain with coefficients `B, D` is, in the standard names, the *dual Hahn* Jacobi matrix (equivalently the difference operator of the Hahn polynomials in `x`); the Jacobi matrix of the Hahn polynomials proper (recurrence in the degree, spectrum `{x/N}`) is the matrix of `X` in the eigenbasis `f` (irreducible tridiagonal by `hahn_dual_irreducible`), so the Leonard pair covers both chains. **Not formalised:** the closed-form entries `A_n`, `C_n` of that Jacobi matrix (Hahn recurrence in the degree for real `α, β`; the natural-`α, β` recurrence is `Racah.hahnQ_rec`), orthogonality of `f`, the travel-time statements and global-class margin |
| `cor:racahheun` (`racah_chain.tex`; folded squared-spin chain `X = diag(q²)`, `Y_{qq} = (Λ-q²)/2`, `Y_{q,q+2} = y_o(q)`, `Y_{0,2} = √2 y_o(0)`, is a Leonard pair, Heun commutant exact) | `W1RacahChain.racah_heun` (`racChain`, `racX`, `racY`, `racBasis`; spectrum `racChain_hasEigenvalue` (`W1RacahSpectrum`), `racY_hasEigenvalue_iff`; duality `rac_dual_irreducible`; relation `rac_tdRel`) | for **every `M`** (`L = 2M`, index `j = q/2`): spectrum exactly `{(2k)²}` (`eq:model`: "both spectra are `{r²}`"); `X` irreducible tridiagonal in an eigenbasis of `Y` (self-duality) hence `heun_commutant`: `H = {X-μ_Q, Y-μ_R}` (midgaps `(x_K+x_K')/2 = Q²+2Q+2`) commutes with `W`, `P`, simple-spectrum Jacobi blocks. Proof without `lem:duality`'s Wigner-`d` involution: tridiagonal relation `[Y,[Y,X]] - 8{Y,X} + 16X = 8(Y-1)(Y-Λ)` (`rac_tdRel`; the doubled link `a_0² = 2y_o(0)²` is compensated at `n = 1` by the vanishing coefficient `2x_1-2x_0-8`, `rac_E0`), spectrum from `Y P = P T`, `P_{kj} = r_k ∏_{t<j}(k²-t²)`, `T` bidiagonal with diagonal `4(M-j)²` (`rac_poly_id`, `rac_shift_up`, `rac_shift_down`). **Not formalised:** `lem:duality` itself (identification with `K_x²`, `K_z²` on the even symmetric subspace, `U = d^L(π/2)`, `U² = 1`), `prop:racahfinite`, `prop:racahtt` |
| `prop:bisp`(i), alternative proof of the Krawtchouk self-duality | `W1KrawtchoukRelation.krawtchouk_tdRel`, `krawtchouk_dual_irreducible_of_relation` | `[Y,[Y,X]] - X/N² = ((p-q)/N²)Y - p/N²` for `X = diag(n/N)`, `Y` the Krawtchouk chain (one-line coefficient identities, `W1TridiagRelation.tdRel_triChain`); with the spectrum `{k/N}` it gives `X` irreducible tridiagonal in an eigenbasis of `Y` with no generating function (the spectrum still uses it). Companion to `W1Krawtchouk.krawX_irreducible` |

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
