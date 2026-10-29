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
  `thm:fqe-general-envelope`, which is not formalized) as an explicit hypothesis `henv`.
- Moment defect and distance stability (`PaperEGenDefect.lean`): `sexticQ`, `defectD`, `entropy_gap_ge_defect`
  (`δ ≥ k 𝒟`, `k = (ln 3 − 1)/(2 ln 2) > 16/225`), `entropy_gap_ge_Q`, `majorant_gap_ge_defect`, `tsallis_gap_ge_defect`, and
  `entropy_gap_critical` (`W₁ = 0`: `δ ≥ k (Q + 5τ/2)`) are unconditional. The distance `d` to the `M₄` orbits is not defined
  in Lean and the HS overlap stability `thm:fqe-global-overlap` (`Q ≥ 1 − Φ ≥ ((6+√6)/12) d² > (7/10) d²`, exact rational
  certificate) is not formalized. `entropy_gap_ge_of_overlap`, `entropy_gap_orbit_stability` (`thm:fqe-orbit-stability`:
  `δ ≥ k ((6+√6)/12) d2 > d2/20`), `entropy_gap_critical_distance` (`eq:fqe-critical-entropy`, constant `(2+√2)/4`),
  `majorant_gap_of_overlap` and `tsallis_gap_of_overlap` (`cor:fqe-orbit-spectral`) are *conditional*: the hypothesis
  `c * d2 ≤ sexticQ ψ` (`d2` standing for `d(ψ)²`) is an explicit argument, never proved or assumed as an axiom.
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
- `lem:seven-joint-scalar-majorant` (AH-6) holds in the paper on all of `[0,∞)²`; it remains the hypothesis `ScalarMajorant`
  (not formalized). `meanEntropy3_le_jointP5_unit` gives `E₃ ≤ 𝒫₅` for every unit vector under `ScalarMajorant (polyH K h) 1`;
  the `497/1000` versions are weaker consequences.
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
  `thm:fqe-global-overlap`, `thm:fqe-general-envelope`, `prop:fqe-critical-envelope`, `prop:seven-resolvent-majorant`, `cor:seven-resolvent-matrix`, `lem:seven-family-symmetric-criticality`,
  the exact transverse Hessian floor `(350 - 6√2005)/4585` of `thm:icolocal`, and the positive-kernel proof of AH-6.

## Gaudin, Racah and bridge modules

The maintained aggregate also imports the current Gaudin metric/rank chain, Racah Weyl-cell modules and B2/Blaschke bridge modules. They are compiled as part of the current aggregate. This high-level map does not attempt to restate every theorem in those families; use the Lean source and theorem-local project updates for exact scope.

## Next source-authorized finite targets

At the current handoff, the cleanest exact candidates are:

1. QI-D T33 exceptional F4 facet representative certificate;
2. QI-D T33 E6/F4 A2 envelope-to-quartic reduction;
3. QI-A T07 finite coding/guessing lemmas with faithful operational hypotheses;
4. the general type-D support/Procrustes bridge if sufficient real-linear-algebra infrastructure is developed.

QI-D T48 and the QI-B B4 flagship remain open research problems, not current theorem-completion targets.
