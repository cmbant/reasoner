module

public import FormalResearch.JE.JECasoratian
public import FormalResearch.JE.JEDefect
public import FormalResearch.JE.JEKernel
public import FormalResearch.JE.JEVolterra

/-!
# Paper J, the abstract engine (Lean)

Umbrella for the Casoratian--Volterra comparison engine of Paper J (`engine.tex`); namespace `FormalResearch.JE`.

* `JECasoratian`: `lem:eng-abel` (Abel--Casoratian identity, hard-edge form, summed form, Cramer identities).
* `JEDefect`: `thm:eng-defect` (exact defect, `h`-parity, Casoratian and Green identities) over an abstract
  `SymplecticLadder`.
* `JEKernel`: `lem:eng-kernel` and the transport formula of `lem:eng-transport`(b).
* `JEVolterra`: `thm:eng-volterra`(a), single patch with the two-node seed.

Not formalised: `thm:eng-corr`, the multi-patch and hard-edge-seed forms of `thm:eng-volterra`, and the model ladders
(Weber, parabolic cylinder).
-/
