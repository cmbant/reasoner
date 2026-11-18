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
* `JEVolterraMulti`: `thm:eng-volterra`(a), general `P` patches, both seeds (hard edge and two-node), with a
  non-vacuity instance.
* `JEVolterraLadder`: `thm:eng-volterra`(b), ladder pairs: the bounds (S1), (S2) and the residuals from the defect
  identities, and the stability corollary `ladder_pair_stability` (`volterra_multi` with these bounds).

Not formalised: `thm:eng-corr`, the patch-dependent envelopes of `thm:eng-volterra`(a) (one global envelope is used),
the defect and envelope bounds of the ladders (hypotheses of the corollary; charts of Section 3), and the model ladders
(Weber, parabolic cylinder).
-/
