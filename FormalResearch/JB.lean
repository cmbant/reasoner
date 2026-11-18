module

public import FormalResearch.JB.JBDefs
public import FormalResearch.JB.JBSchur
public import FormalResearch.JB.JBRatio
public import FormalResearch.JB.JBGlue
public import FormalResearch.JB.JBPolar
public import FormalResearch.JB.JBFermion
public import FormalResearch.JB.JBOneStepDef
public import FormalResearch.JB.JBOneStepAux
public import FormalResearch.JB.JBOneStepChart
public import FormalResearch.JB.JBOneStep
public import FormalResearch.JB.JBThmB

/-!
# Paper J, Theorem B reduction (Lean, stage 1)

Umbrella for the Lean formalisation of the matrix lemmas of Paper J's Theorem B reduction
(`thmB.tex`, section "Three lemmas on matrices"); namespace `FormalResearch.JB`.

* `JBDefs` : the Schur multiplier bound `IsSchurBdd` and its closure properties.
* `JBSchur` : `lem:thb-schur`, `C²` form (`jb_schur_of_C2`, reciprocals and quotients).
* `JBRatio` : `lem:thb-ratio` (`jb_ratio`).
* `JBGlue` : `lem:thb-glue` (`jb_glue`, `jb_glue_rev`).
* `JBPolar` : `lem:thb-polar` (`jb_polar`).

* `JBFermion` : `cor:fermions` (`jb_fermions`, parts (i)-(iii) with the paper's constants).
* `JBOneStepDef` : the one-step criterion `thm:thb-onestep`: `Chart`, `OneStepInputs`, `OneStepReduction`
  (statement) and a toy non-vacuity instance.
* `JBOneStepAux`, `JBOneStepChart`, `JBOneStep` : its proof (`jb_onestep : OneStepReduction cs`).
* `JBThmB` : `thm_B_conditional` (paper quantifier order, `D = L/h`, family of one-step inputs).

Not formalised: the verification of the inputs (I1)-(I5) for actual Jacobi matrices (`prop:thb-inputs`, Theorem A(ii)
and the charts), so `thm_B_conditional` is conditional on a family of `OneStepInputs`; `rem:thb-entropy`; the sharper
assembly for orthogonal columns.

The finite
Schur lemma, ratio lemma, polar repair and fermion bounds of the Jacobi-operator package
(`FormalResearch.MatrixAnalysis.JacobiOp*`) are reused, not redone.
-/
