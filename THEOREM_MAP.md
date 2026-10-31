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

Source: `QI-B/paper/invariant_discrimination_exponents.tex` `prop:u1`.

Lean proves the exact scalar factor-two exponent relation for the source family; the twirl/binomial/operational Chernoff derivation remains external.

### B1 apolar kernel (`FormalResearch/QIB1`)

Source: `QI-B/B1-apolar/results/apolar_finite_defect_results.tex` (`D_F = 3 d_x^2 d_y - d_y^3`), lane record `QI-B/B1-apolar/notes/STATUS_MATRIX.md`.

Lean proves, for every `d >= 3`, that the monomial-coefficient matrix of `D_F` has full row rank `d-2` over `Q` and `R`, that its kernel has dimension 3, and that over `R` the kernel is spanned by the three coherent powers at `b = 0, +-sqrt 3`. The factorization `lambda_d I - E_d = D_F^dagger R_d D_F`, `R_d > 0` and all finite-defect/Hahn row identities remain external.

### B2 Hamming/Krawtchouk phase algebra (`FormalResearch/QIB2`)

Source: `QI-B/B2-hamming/results/three_band_hamming_heat_kernel.tex`, section "Exact Hamming/Krawtchouk phase algebra" (`eq:hammingU`).

Lean proves the scalar/Boolean-cube content: Krawtchouk coefficient formula and generating function, the Bose--Mesner eigenaction on a Walsh character, the canonical gate phase `i^|T|` for every Walsh label, and the `choose d m` multiplicity of weight `m`. The two-qubit swap operators, the projectors `E_m` and the operator identity on `(C^4)^(tensor d)` remain external. `Bridges/B2BlaschkeMultiplicityRank.lean` uses `QIB2.card_WalshWeightIndex`.

### B4 late source status

QIprojects now proves the flagship (`thm:flagship` in `QI-B/paper/invariant_discrimination_exponents.tex`: `F_C = F_K = 1/2`, `xi_inv = log 2`), but the theorem itself is not formalized (QIprojects `docs/lean_status.md` records what the `QIB` modules cover). Any B4 formalization must match a proved source theorem (check `QI-B/B4-orbit-bergman/notes/CORRECTIONS.md` and `QI-B/paper/CORRECTIONS.md` first) and keep the class of each statement.

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
`ResearchNotes/QI/four_qubit_entropy/` (theorems `thm:fqe-moment`, `lem:fqe-purity`, `thm:fqe-entropy-max`).

The development is the Lean companion of QIprojects Paper E (`ResearchNotes/QI/four_qubit_entropy/`) and is developed
here; QIprojects holds no Lean source. Beyond the entropy maximum below it contains the equality case, one-cut rigidity,
the cubic-majorant criterion, Tsallis/Rényi bounds with equality, the HS/cluster crossing, convex-roof ceilings,
`Tradeoff.lean` (the `n = 4` purity–time-reversal tradeoff `π₂ ≥ 1/3 + τ/6`, optimal coefficient, three Bell-pairing zeros of
`F`), and `SevenQubitIcoState.lean` and `SevenQubitIcoPurity.lean` (the seven-qubit icosahedral coefficient tensor of `thm:ico`:
unit norm, maximally mixed one-qubit marginals, the purity polynomial of every three-qubit cut (35) and pair (21)
derived from the tensor, the mean three-body purity `121/917 + (1048/525)(x−37/524)²` on the family with unique minimum at
`x = 37/524`, and the cut and pair purities there; `SevenQubitIcoCert.lean`/`SevenQubitIcoSpectrum.lean`: the spectrum of
every three-qubit cut, `(4α²)⁶,(3α²+β²)²` avoiding the special site and `8α²,(4α²)⁵,(α²+β²)²` containing it;
`SevenQubitIcoEntropy.lean`: the mean three-body entropy of the family is strictly concave with a unique maximiser strictly
between `0` and `37/524`; the pair spectra and the numerical value of the maximiser are not formalized). Kernel `decide +kernel` only; no compiler axiom.

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
  `entropy_gap_critical` (`W₁ = 0`: `δ ≥ k (Q + 5τ/2)`) are unconditional. The distance `d` to the `M₄` orbits is not defined
  in Lean and the HS overlap stability `thm:fqe-global-overlap` (`Q ≥ 1 − Φ ≥ ((6+√6)/12) d² > (7/10) d²`, exact rational
  certificate) is not formalized. `entropy_gap_ge_of_overlap`, `entropy_gap_orbit_stability` (`thm:fqe-orbit-stability`:
  `δ ≥ k ((6+√6)/12) d2 > d2/20`), `entropy_gap_critical_distance` (`eq:fqe-critical-entropy`, constant `(2+√2)/4`),
  `majorant_gap_of_overlap` and `tsallis_gap_of_overlap` (`cor:fqe-orbit-spectral`) are *conditional*: the hypothesis
  `c * d2 ≤ sexticQ ψ` (`d2` standing for `d(ψ)²`) is an explicit argument, never proved or assumed as an axiom.
  For critical states `d2` is the real `dist2` (`CriticalOrbitPhi.lean`) and the hypothesis is discharged except for the
  all-state comparison `Q ≥ 1 - Φ` when `Φ ≥ 1/2`: see "Branch `paper-e-ah6`: sharp critical-state orbit stability" below.
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
  the equality cases and sharpness are not formalized there. `two_flat_rigidity` is the critical specialization
  `W₁ = 0`; the Schmidt-rank-two consequence `two_flat_rank` holds for every unit state.
- `lem:seven-entropy-linear-purity`: proved with the sharp slope, `3 - S ≥ (7 log₂ 7/48)(8 tr ρ² - 1) ≥ (49/120)(8 tr ρ² - 1)
  ≥ (2/5)(8 tr ρ² - 1)` (`LinPur.entropy_linear_purity_sharp_nats`, `_rat_nats`, `entropy_linear_purity_nats`); the equality
  cases are not formalized. The competitor band and the eigenvalue cap `497/1000` use the slope `2/5`.
- `lem:seven-joint-scalar-majorant` (AH-6) holds in the paper on all of `[0,∞)²`; it is proved in branch `paper-e-ah6` for the
  explicit coefficients (`AH6.joint_scalar_majorant`, see "Branch `paper-e-ah6`" below). `meanEntropy3_le_jointP5_unit` gives
  `E₃ ≤ 𝒫₅` for every unit vector under `ScalarMajorant (polyH K h) 1`; the `497/1000` versions are weaker consequences.
- `prop:stab7`: not formalized. The paper's proof is analytic (Pauli and shadow enumerators with integer coefficients);
  `SevenQubitStab7` has the witness `π₃ = 19/140` and a reduction conditional on a statement about all `2^21` graph states.
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
- Not formalized, new in the current paper:
  `thm:fqe-global-overlap`, `prop:seven-resolvent-majorant`, `cor:seven-resolvent-matrix`, `lem:seven-family-symmetric-criticality`,
  the exact transverse Hessian floor `(350 - 6√2005)/4585` of `thm:icolocal` (the positive-kernel proof of AH-6 is formalized in branch `paper-e-ah6`).

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
  Not formalized: the full classification of the equality set (the `τ = 0` zero set of `H`, and the orbit description for `τ > 0`).
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
- Equality cases of `thm:fqe-general-envelope` / `prop:fqe-critical-envelope`: only the sharpness family and the `W₁ = 0` forcing above.
  A degree-8 SOS search in the `v`-coordinates of `G(v)` (330x330 Gram) did not return a usable certificate within the session.
- `prop:stab7` identities (Pauli/shadow enumerators) and the second inequality of `(TF)` in `prop:fqe-two-flat-rigidity`: not attempted.
  The `W₁/4` term of `(TF)` was already covered by `two_flat_cross_cost_12/13/14`.

## Gaudin, Racah and bridge modules

The maintained aggregate also imports the current Gaudin metric/rank chain, Racah Weyl-cell modules and B2/Blaschke bridge modules. They are compiled as part of the current aggregate. This high-level map does not attempt to restate every theorem in those families; use the Lean source and theorem-local project updates for exact scope.

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
  comparison `thm:fqe-global-overlap`, which is not formalized and is used only when `Φ ≥ 1/2` (there `3/2-2Φ ≤ 1-Φ`).
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

Not formalized: the null-critical refinement (`eq:fqe-null-critical-sharp`, `Φ ≥ (2+√3)/6`, `Q ≥ 3(1-Φ)/(4-√3)`), `thm:fqe-p1-sharp`
(`C_*`), and `thm:fqe-global-overlap` itself.

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
