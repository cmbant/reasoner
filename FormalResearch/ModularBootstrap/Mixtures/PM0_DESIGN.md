# PM-0 design note (mixtures, interface)

Labels: `pmix:rebase` (PM.1), `pmix:weight` (PM.2, W1-W4), `pmix:crossing` (PM.3), `pmix:jets` (PM.13) of
`CFT/modular_bootstrap/paper/positive_mixtures.tex`. Namespace `FormalResearch.ModularBootstrap.Mixtures`,
files only under `Mixtures/`. No existing file is edited; every generalisation is proved here and the in-place
re-derivation of the old fixed-weight declarations is a follow-up (see the final notes of the PM-0 report).

## Decision: finite exponential-sum (atomic shift measure), not an abstract axioms structure

The paper's *common source class* is `V(t) = int K_{a-r}(t) dlambda(r)` for a finite signed measure `lambda` on
`[0, S_lambda]` with a comparison floor `V >= d_lambda V_{w,Q_0}`; a rebased positive mixture is the atomic case
`lambda = sum d_i c_{i,u} delta_{r_i+u}`. Lean takes the **atomic** case: `ShiftSource` = weight `w`, a finite
index type, real coefficients and nonnegative shifts, `cardyV a t = sum_j coef_j kernelK w (a - shift_j) t`.

Why atomic, not an abstract axioms structure:
* the existing fixed-weight stack is written against `FixedWeightProblem.cardyV`, which already *is* such a sum
  (atoms = subsets of the null shifts, coefficients `(-1)^|s|`); `ShiftSource.ofProblem` embeds it with
  `cardyV = cardyV` by `rfl`, so the new definitions specialise to the old ones definitionally (the bridge);
* the common-source hypotheses are exactly comparisons `d V_{Q_0} <= V <= C K_a`; every fact PM.2/PM.3 need follows
  from the *already proved* fixed-weight theorems for `Q_0` and for `Q = 1` (`trivialProductProblem`) by comparison,
  so the heavy analysis (Hankel continuation, kernel/band floors, Cardy asymptotes) is reused, not re-proved;
* the one genuinely new analysis, the Cardy asymptote of a single shifted kernel `K_{a-r}`, is *derived* from the
  existing product theorems applied to the two one-factor problems `Q = 1` and `Q = 1 - q^r`
  (`K_{a-r} = K_a - V_{(r)}`), uniformly over finitely many atoms; no new Bessel analysis;
* an abstract axioms structure would only repackage W1-W4 and still need a concrete instance (the same work).
  The structure `SourceAxioms src c'` below *is* that axioms structure, with `FixedWeightAxioms` as the special case
  (`FixedWeightAxioms.toSourceAxioms`), so downstream packages can be written against it (also for real `w` later).
General Borel `lambda` (non-atomic continuum of shifts) is not formalised: it is not needed for mixtures and would
need measurability/Fubini plumbing at every step. Recorded as a limitation.

## Files (each builds with guards; list in `/home/user/scratch/lean/agent_pm0_modules.txt`)
1. `Source.lean`: `ShiftSource`, `cardyV`, reduced form, `TestClass`, `gVac`, thresholds, `ofProblem` bridge, Laplace identity.
2. `Mixture.lean`: `MixtureData`, flattening `toSource`, amplitude/source functions, `pmix:rebase` (a).
3. `RebaseAnalysis.lean`, `RebaseVague.lean`: `pmix:rebase` (b), (c) (charts `u_n`, `J_n`, reverse window; vague-limit transfer).
4. `CommonSource.lean`: common source class, `pmix:weight` (a) (Laplace, sandwich, floor, positivity).
5. `ShiftAsymptotics.lean`, `SourceAxioms.lean`, `WeightAxioms.lean`: `pmix:weight` (b), (c).
6. `CrossingPort.lean` (unconditional port of `Crossing/SumRule.lean` to `ShiftSource`), `CrossingCommon.lean`
   (`CrossingBounds` from the floor), `CrossingA.lean` (`pmix:crossing` (a)), `CrossingB.lean` (`pmix:crossing` (b)).
7. `Jets.lean`, `JetsJensen.lean`: the parts of `pmix:jets` that do not need the five-term outer-function machinery
   (hypotheses of `ctu:jets`, shift integral `ξ_*/√2`, Jensen comparison).

## Scope conventions
* "for all sufficiently large n" is `a >= a0` (charge threshold); fixed-charge statements take the floor at that charge.
* Every result is **proved** (no hypothesis restating a conclusion); anything resting on `ctu:jets`/`ctu:common-functional`
  at a general amplitude is marked not done (those are FIVE-0 outputs, planned).
