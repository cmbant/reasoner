module

public import FormalResearch.Jacobi.Basic
public import FormalResearch.Jacobi.Interlacing
public import FormalResearch.Jacobi.Oscillation
public import FormalResearch.Jacobi.Reconstruction
public import FormalResearch.Jacobi.CombesThomas
public import FormalResearch.Jacobi.DirichletBlocks
public import FormalResearch.Jacobi.DirichletIntervals
public import FormalResearch.Jacobi.AgmonEnergy
public import FormalResearch.Jacobi.AgmonDeletion
public import FormalResearch.MatrixAnalysis.MaskedFrobenius
public import FormalResearch.MatrixAnalysis.SpectralResidual
public import FormalResearch.MatrixAnalysis.SignLocking

/-!
# Finite Jacobi matrices (generic library for the Weyl P5/M7 notes)

Elementary theory of real symmetric tridiagonal (Jacobi) matrices with nonzero links, and the generic
finite-matrix lemmas used by PR 250 (P5/M7):

* `Jacobi.Basic` : the matrix, the recurrence polynomials `P_j`, eigenvalues = roots of `P_n`, simple
  eigenspaces, the eigenvector recurrence (Theorem ER, general form);
* `Jacobi.Interlacing`, `Jacobi.Oscillation` : strict interlacing of the zeros of consecutive leading
  blocks and the Sturm oscillation sign formula (SP.1);
* `Jacobi.Reconstruction` : Theorem ER (eqs. (ER.1), (ER.2));
* `Jacobi.CombesThomas`, `Jacobi.DirichletBlocks`, `Jacobi.DirichletIntervals` : the Combes–Thomas
  weighted resolvent estimate, Theorem DB.1/DB.2 and the Frobenius deletion bound (DB.3);
* `Jacobi.AgmonEnergy`, `Jacobi.AgmonDeletion` : the exact weighted energy identity (AG.3), AG.1/AG.2
  and the Frobenius deletion bound (AG.4);
* `MatrixAnalysis.MaskedFrobenius` (REG.1), `MatrixAnalysis.SpectralResidual` (Theorem 1),
  `MatrixAnalysis.SignLocking` (Theorem 2).
-/
