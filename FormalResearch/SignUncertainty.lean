module

public import FormalResearch.SignUncertainty.ClarkTwoNode
public import FormalResearch.SignUncertainty.HermiteBiehlerUniq
public import FormalResearch.CohnElkies

/-!
# Sign Uncertainty and Cohn–Elkies Bootstrap

Umbrella collecting sign-uncertainty theorems and Cohn–Elkies analytic lemmas:

* `FormalResearch.SignUncertainty.ClarkTwoNode`: Clark two-node sign uncertainty and equality
  characterization (`CFT/common/clark_airy.tex`, Theorem 1.2).
* `FormalResearch.SignUncertainty.HermiteBiehlerUniq`: polynomial Hermite–Biehler uniqueness
  and `m = 2` `L^1` norm identity (`CFT/common/clark_airy.tex`, Lemma `H.2a` and `(eq:hb-two-node-norm)`).
* `FormalResearch.CohnElkies`: Stieltjes/cardinal resolvent, Mellin–Airy, and Fourier interpolation
  lemmas.
-/
