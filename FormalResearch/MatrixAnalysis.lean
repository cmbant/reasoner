module

public import FormalResearch.MatrixAnalysis.VectorNorm
public import FormalResearch.MatrixAnalysis.HelstromPure
public import FormalResearch.MatrixAnalysis.TraceNorm
public import FormalResearch.MatrixAnalysis.TraceNormGeneral
public import FormalResearch.MatrixAnalysis.TraceDistance
public import FormalResearch.MatrixAnalysis.KernelQuant
public import FormalResearch.MatrixAnalysis.ExtremeCriterion
public import FormalResearch.MatrixAnalysis.Spectral.MinMax
public import FormalResearch.MatrixAnalysis.Spectral.Weyl
public import FormalResearch.MatrixAnalysis.Spectral.KyFan
public import FormalResearch.MatrixAnalysis.Spectral.SpecMap
public import FormalResearch.MatrixAnalysis.Spectral.Lidskii
public import FormalResearch.MatrixAnalysis.Spectral.HoffmanWielandt
public import FormalResearch.MatrixAnalysis.Spectral.KyFanProj
public import FormalResearch.MatrixAnalysis.Spectral.WeylMatrix
public import FormalResearch.MatrixAnalysis.Spectral.SingularWeyl
public import FormalResearch.MatrixAnalysis.Spectral.FanHoffman
public import FormalResearch.MatrixAnalysis.Spectral.FanHoffmanPolar

/-!
# Matrix analysis

General finite-dimensional matrix facts used across the corpus: the Hermitian trace norm and its
variational characterisation (`TraceNorm`), the trace norm of a non-Hermitian matrix (`TraceNormGeneral`),
pure-state Helstrom (`HelstromPure`), witness distance bounds (`TraceDistance`), the quantitative
kernel-penalty lift (`KernelQuant`) and the supported-face extremality criterion (`ExtremeCriterion`).

The `Spectral` submodules (namespace `FormalResearch.MatrixAnalysis.Spectral`) formalise the perturbation
theory of Hermitian spectra with Mathlib's sorted eigenvalues: Courant–Fischer (`MinMax`), Weyl and Cauchy
interlacing (`Weyl`), Ky Fan (`KyFan`, `KyFanProj`), Lidskii–Wielandt (`Lidskii`), von Neumann and
Hoffman–Wielandt (`HoffmanWielandt`), their matrix forms (`WeylMatrix`), Weyl for singular values
(`SingularWeyl`) and the operator-norm Fan–Hoffman polar-factor theorem (`FanHoffman`, `FanHoffmanPolar`);
`SpecMap` is the functional-calculus helper.

The masked-Frobenius, spectral-residual and sign-locking lemmas (`MaskedFrobenius`, `SpectralResidual`,
`SignLocking`) belong to the Jacobi programme and are imported by the aggregate `FormalResearch.Jacobi`.
The `JacobiOp*` modules (Paper J operator package: Schur multiplier, normalisation ratio, polar-factor repair,
free-fermion bounds) are likewise outside this aggregate; their umbrella is `FormalResearch.MatrixAnalysis.JacobiOp`.
-/
