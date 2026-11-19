module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftW2
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftSigns3

/-!
# Paper J, Layer 2 (L2.C7): `PropThaW2` proved

`propThaW2_proved`: the frozen statement `PropThaW2` (prop:tha-W2 (1)--(4)), for every soft-edge chart pair `CL`, `CR` with
`SoftMirror CL CR`, `ParabolicCylinderFacts U V cPC CPC` and `Lm >= 1`, with no further premise: `propThaW2_proved_of_signs`
(`SoftW2.lean`) with its premise `SoftCountHyps` discharged by `softCountHyps_proved` (`SoftSigns3.lean`, Step 6 (ii), (iii)).
`1 <= m`, `SoftMirror` and `Lm >= 1` are premises of the frozen statement itself; `StdAssump` is one too (unused).
Differences from the paper: counting windows `Phi = pi mu_0`, `eps = pi h/8` instead of `pi mu~`, `C h^{m+1}` (see `SoftCountHyps`);
chart fields added in rounds 7-9 (F-W2-17..20) in `SoftEdgeChart`, `ParabolicCylinderFacts.U_pos` (stated there, not used here).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]
variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

/-- **prop:tha-W2** (items (1)--(4)), proved. -/
theorem propThaW2_proved (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)
    (Cs0 : ℝ) (cPC CPC : ℝ) : PropThaW2 Fz P m q U V CL CR Cs0 cPC CPC := by
  intro hf hm hLm hM r hr
  exact propThaW2_proved_of_signs (CL := CL) (CR := CR) Cs0 (softCountHyps_proved CL CR hM hf hm hLm Cs0) hf hm hLm hM r hr

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaW2_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propThaW2_proved

end FormalResearch.JacobiEigenvectors.TheoremA

end
