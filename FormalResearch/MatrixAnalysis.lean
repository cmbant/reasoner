module

public import FormalResearch.MatrixAnalysis.VectorNorm
public import FormalResearch.MatrixAnalysis.HelstromPure
public import FormalResearch.MatrixAnalysis.TraceNorm
public import FormalResearch.MatrixAnalysis.TraceNormGeneral
public import FormalResearch.MatrixAnalysis.TraceDistance
public import FormalResearch.MatrixAnalysis.KernelQuant
public import FormalResearch.MatrixAnalysis.ExtremeCriterion

/-!
# Matrix analysis

General finite-dimensional matrix facts used across the corpus: the Hermitian trace norm and its
variational characterisation (`TraceNorm`), the trace norm of a non-Hermitian matrix (`TraceNormGeneral`),
pure-state Helstrom (`HelstromPure`), witness distance bounds (`TraceDistance`), the quantitative
kernel-penalty lift (`KernelQuant`) and the supported-face extremality criterion (`ExtremeCriterion`).
-/
