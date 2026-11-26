# PM-1 design note (ramped comb, smooth transfer, `O(1)` law for mixtures)

Labels: `pmix:punif` (PM.4), `pmix:ramped` (PM.5), `pmix:smooth` (PM.6), `pmix:o1` (PM.7) of
`CFT/modular_bootstrap/paper/positive_mixtures.tex`. Namespace `FormalResearch.ModularBootstrap.Mixtures`; new files only
in `Mixtures/`; no existing file is edited, so the in-place re-derivation of the W-P6 declarations is a follow-up.

## What the paper's four labels need, and what Lean already has

* `pmix:punif` and `pmix:ramped` do not involve the Cardy weight at all: the Airy-profile estimate and the bumped
  ramped comb depend on the weight `w` only. Lean has them at every weight, source free: `lemma_P_unif`,
  `pUnif_integral_le`, `rampedW_package` (`Upper/Ramped/PUnif`, `RampedVacuumProfile`) and `rampedBumped_positive`,
  `rampedBumped_k7`, `rampedThreshold` (`RampedBumpPositive`, `RampedThreshold`). PM-1 only *packages* them under the
  paper's labels (`Mixtures/Punif.lean`, `Mixtures/Ramped.lean`).
* `pmix:smooth` is the one place where the weight enters: the integral `∫ h_0^{(p)} V_n` is bounded using only (i) a
  smooth positive amplitude `q` with `V_n(n x^2/3) = (2x)^p A(x) as(n L(x)) (1 + O(1/n))` on the Langer window, and
  (ii) the far-band bound with `K_2 = w - 1`. W-P6 proves it for `V = prob.cardyV`; the proof uses `prob` only through
  these two properties, `V >= 0`, continuity and the integrability of `h V`.
* `pmix:o1` assembles lower and upper halves for the common source class.

## Decision: a hypothesis structure for the weight (`SmoothWeight`), instantiated by `ShiftSource` + `FloorData`

`SmoothWeight w` (file `SmoothWeight.lean`) packages exactly the hypotheses of `pmix:smooth`: a weight family
`V : c' -> t -> ℝ`, an amplitude `A : ℝ -> ℝ` (so `q(x) = (2x)^{w-1} A(x) / (1 - e^{-4πx})^2`), the real Cardy asymptote
(additive form, equivalent to the multiplicative `O(1/n)` of the paper since `q` is bounded below), `A` positive at `ξ_*`
and Lipschitz on the window, the far-band bound `CardyFarBoundP (w-1) V (ξ_* + 1/2)` (this *is* hypothesis (ii) with
`K_2 = w - 1`), nonnegativity, continuity and the domination `V <= C K_a` (only used for integrability of `h V`, and
satisfied by every Cardy weight). The structure is *not* a restatement of the conclusion.

The proofs of W-P6 are re-run against it: `theta_boundS`, `rampedBump_pointwise_S` are the abstract-amplitude copies of
`theta_boundW`, `rampedBump_pointwise`, and `smooth_vacuum` (`pmix:smooth`) is `rampedBumpVacuum` with `FKc (qProb prob)`
replaced by `FKc (q_A)`. The abstract far/lobe/props lemmas replace `cardyFarBoundP_prob`, `cardyV_nonneg`,
`integrableOn_mul_cardyV`.

`ShiftSource.smoothWeight` (file `RampedSource.lean`) builds the structure for a source with floor, from
`pmix_weight_b` (asymptote, `A = src.ampl`, `A >= d_λ Q_0 > 0`), `0 <= V <= ‖λ‖_TV K_a` and
`cardyFarBoundP_prob (trivialProductProblem w)` for the far band. No Bessel analysis is added.

The comb and its test function are those of W-P6 for the *trivial product* `Q ≡ 1` of weight `w`
(`rampedBumpG (trivialProductProblem w hw) P c'`): `rampedBumpG` depends on the problem only through `prob.w`.
Membership in the source test class and the vacuum identity come from `pmix_crossing_b` (PM-0) plus
`FloorData.At.testClass_of_trivial`, using the decay bounds of `rampedBumped_k7` for `Q ≡ 1`.

## The lower half

Theorem W1'(1) is *not* re-run against `SourceAxioms` (the chain `FixedWeightBand/*` is tied to `FixedWeightProblem`).
For positive mixtures it is not needed: the paper's "sharper component comparison" (a weakly feasible test for the mixture
is weakly feasible for some component `i` at `n_i = n - 12 r_i`, since `V_mix >= d_i V_i >= 0` and `g_vac,mix = ∑ d_i g_vac,i`)
reduces the lower bound to the *single component* weak bound of `theoremFTLFW_W_of_YVFor`, which is proved. This gives the
lower half of `pmix:o1` for every `MixtureData` without rebasing or (W1)-(W4). The lower half for a general signed common
source (`CommonSource` with signed `λ`) needs Theorem W1'(1) on `SourceUniformAxioms`: not done.

## Scope conventions

* Charges: statements are for `c ≥ c₂` (`c = c̃ = n`, `a = c/12`), as in PM-0.
* The paper's `+ O(1)` is `D_+`/`D_-` existentially quantified; no numerical constants are quoted.
* The vacuum step of `pmix:smooth` is stated at `d = M_0 c'^{-1/3}` for the `M_0` it produces (the paper's `d = M n^{-1/3}`).
