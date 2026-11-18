module

public import FormalResearch.JacobiEigenvectors.Engine.Casoratian
public import FormalResearch.JacobiEigenvectors.Engine.Defect
public import FormalResearch.JacobiEigenvectors.Engine.Kernel
public import FormalResearch.JacobiEigenvectors.Engine.Volterra
public import FormalResearch.JacobiEigenvectors.Engine.VolterraMulti
public import FormalResearch.JacobiEigenvectors.Engine.VolterraLadder
public import FormalResearch.JacobiEigenvectors.Engine.Green
public import FormalResearch.JacobiEigenvectors.Engine.LadderStability

/-!
# Paper J, the abstract engine (Lean)

Umbrella for the Casoratian--Volterra comparison engine of Paper J (`engine.tex`); namespace `FormalResearch.JacobiEigenvectors.Engine`.

* `Casoratian`: `lem:eng-abel` (Abel--Casoratian identity, hard-edge form, summed form, Cramer identities).
* `Defect`: `thm:eng-defect` (exact defect, `h`-parity, Casoratian and Green identities) over an abstract
  `SymplecticLadder`.
* `Kernel`: `lem:eng-kernel` and the transport formula of `lem:eng-transport`(b).
* `Volterra`: `thm:eng-volterra`(a), single patch with the two-node seed.
* `VolterraMulti`: `thm:eng-volterra`(a), general `P` patches, both seeds (hard edge and two-node), with the transfer
  condition (S3) either a hypothesis or derived at forbidden overlaps, patch-dependent envelopes
  (`volterra_multi_patchwise`: the patch envelopes are glued into the single family of (S2)), and non-vacuity instances (exact, and perturbed
  with `ε > 0`, `ψ ≠ ψ̂`, for both seeds).
* `Green`: the Green identities of a finite Jacobi window (`casD` constant in `n`, `D' = sum p q`), generic in the bonds.
* `LadderStability`: `LadderData.stability`, the stability of a chain of per-patch ladder pairs (`Charts.LadderData.Stability`),
  from `volterra_multi` and the per-patch ladder lemmas.
* `VolterraLadder`: `thm:eng-volterra`(b), ladder pairs: the bounds (S1), (S2) and the residuals from the defect
  identities, and the stability corollaries `ladder_pair_stability` (`volterra_multi` with these bounds) and
  `ladder_pair_stability_forbidden`.

Not formalised: `thm:eng-corr`, the bounded-overlap derivation of (S3), the defect and envelope bounds of the ladders (hypotheses of the corollaries; charts
of Section 3), and the model ladders (Weber, parabolic cylinder).  The relations `det Π± = 𝒟±²`, `Π₋Π₊ = 𝒟₊²` and (SM3)
of `SymplecticLadder` are required on all of `ℝ²` rather than on the paper's domain.
-/
