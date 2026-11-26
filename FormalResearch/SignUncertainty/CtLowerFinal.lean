module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.CtBoasEventual

/-!
# `thm:ct-lower` with `ct:boas` discharged

`ct_lower : CtLowerInputs → CtLowerStatement`: `ct_lower_of_boas` (`CtLower`) with the proved `ct_boas_concrete`
(`CtBoasEventual`).  The only remaining field of `CtLowerInputs` is `dyadic` (`ct:dyadic` (4)).  Kept in its own module
because the proof of `ct_boas_concrete` imports `CtLower` (through `FctMainHankel`).
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

/-- **`thm:ct-lower` (`eq:ct-lower`, left half) from `CtLowerInputs`** (one field, `ct:dyadic` (4)). -/
theorem ct_lower (I : CtLowerInputs) : CtLowerStatement :=
  ct_lower_of_boas I ct_boas_concrete

/-- info: 'FormalResearch.SignUncertainty.ct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower

end FormalResearch.SignUncertainty
