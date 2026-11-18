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

The finite
Schur lemma, ratio lemma, polar repair and fermion bounds of the Jacobi-operator package
(`FormalResearch.MatrixAnalysis.JacobiOp*`) are reused, not redone.
-/
