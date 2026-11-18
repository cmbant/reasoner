module

public import FormalResearch.JE.JECasoratian
public import FormalResearch.JE.JEDefect
public import FormalResearch.JE.JEKernel
public import FormalResearch.JE.JEVolterra
public import FormalResearch.JE.JEVolterraMulti
public import FormalResearch.JE.JEVolterraLadder

/-!
# Paper J, the abstract engine (Lean)

Umbrella for the Casoratian--Volterra comparison engine of Paper J (`engine.tex`); namespace `FormalResearch.JE`.

* `JECasoratian`: `lem:eng-abel` (Abel--Casoratian identity, hard-edge form, summed form, Cramer identities).
* `JEDefect`: `thm:eng-defect` (exact defect, `h`-parity, Casoratian and Green identities) over an abstract
  `SymplecticLadder`.
* `JEKernel`: `lem:eng-kernel` and the transport formula of `lem:eng-transport`(b).
* `JEVolterra`: `thm:eng-volterra`(a), single patch with the two-node seed.
* `JEVolterraMulti`: `thm:eng-volterra`(a), general `P` patches, both seeds (hard edge and two-node), with the transfer
  condition (S3) either a hypothesis or derived at forbidden overlaps, and non-vacuity instances (exact, and perturbed
  with `ε > 0`, `ψ ≠ ψ̂`, for both seeds).
* `JEVolterraLadder`: `thm:eng-volterra`(b), ladder pairs: the bounds (S1), (S2) and the residuals from the defect
  identities, and the stability corollaries `ladder_pair_stability` (`volterra_multi` with these bounds) and
  `ladder_pair_stability_forbidden`.

Not formalised: `thm:eng-corr`, the gluing of patch-dependent envelopes into the single family `M, W` of `(S2)`, the
bounded-overlap derivation of (S3), the defect and envelope bounds of the ladders (hypotheses of the corollaries; charts
of Section 3), and the model ladders (Weber, parabolic cylinder).  The relations `det Π± = 𝒟±²`, `Π₋Π₊ = 𝒟₊²` and (SM3)
of `SymplecticLadder` are required on all of `ℝ²` rather than on the paper's domain.
-/
