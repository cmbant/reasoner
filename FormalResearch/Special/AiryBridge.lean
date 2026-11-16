module

public import FormalResearch.Special.AiryIdentities
public import FormalResearch.Special.SturmAiryZeros

/-!
# Bridge: `Ai` as a solution in the Sturm/Prüfer layer

`FormalResearch.Special.IsAirySol y y'` (over `ℝ`) is exactly
`FormalResearch.Special.SturmAiry.IsSol (fun x => x) y y'`.  This module records the equivalence and the
instance for `Ai`, so that the generic results of `SturmAiry*` and `AiryPrufer*` (simple zeros, Sturm
separation and comparison, infinitely many zeros on `(-∞, 0]`, at most one zero on `[0, ∞)` for
nontrivial solutions, the Prüfer lift and zero counting, Clark-node interlacing) apply to `Ai` and to every
real solution built from it.

Not formalised: the real `Bi'` (only the complex `airyBiC` and its derivative are defined) and hence the
bridge for `Bi`; for `Ai` all `IsSol` statements follow.
-/

@[expose] public section

namespace FormalResearch.Special

/-- `IsAirySol` over `ℝ` is `SturmAiry.IsSol` for `q x = x`. -/
theorem isSol_of_isAirySol {y y' : ℝ → ℝ} (h : IsAirySol y y') :
    SturmAiry.IsSol (fun x => x) y y' :=
  ⟨fun x => (h x).1, fun x => (h x).2⟩

/-- The converse direction. -/
theorem isAirySol_of_isSol {y y' : ℝ → ℝ} (h : SturmAiry.IsSol (fun x => x) y y') :
    IsAirySol y y' :=
  fun x => ⟨h.hasDerivAt x, h.hasDerivAt' x⟩

/-- `(Ai, Ai')` is a solution of `y'' = x y` in the sense of the Sturm/Prüfer layer. -/
theorem isSol_airyAi : SturmAiry.IsSol (fun x => x) airyAi airyAi' :=
  isSol_of_isAirySol isAirySol_airyAi

/-- info: 'FormalResearch.Special.isSol_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.isSol_airyAi

end FormalResearch.Special
