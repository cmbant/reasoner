module

public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem
public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.Regularity
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.TransferCoefficients
public import FormalResearch.JacobiEigenvectors.Charts.ChartInputs
public import FormalResearch.JacobiEigenvectors.TheoremA.Comparison
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryStatements
public import FormalResearch.JacobiEigenvectors.TheoremA.EigenvalueStatements
public import FormalResearch.JacobiEigenvectors.TheoremB.ComparisonMatrix
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkSchur
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceBulk
public import FormalResearch.JacobiEigenvectors.TheoremB.TwoOrdersBulk
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkOneStep
public import FormalResearch.JacobiEigenvectors.TheoremA.Count
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkProof
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkConj1
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftProof
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftItem1
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftEigen
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryCollision
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryMargins
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryAll
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftInt
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftMorse
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftUnif
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftSymbol
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoft
public import FormalResearch.JacobiEigenvectors.TheoremA.TruncationSM
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowEnvelopes
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass2
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftQuant
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTails
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTails2
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCovered
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhase
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumTaylor
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumUnique
public import FormalResearch.JacobiEigenvectors.TheoremA.SmoothSpectrum
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkWindows

/-!
# Paper J (Jacobi eigenvectors): conditional pipeline, statement freeze (Lean)

Umbrella **stub** for the statement freeze of the Layer 2/3 formalisation of Paper J (every Bohr--Sommerfeld eigenvalue and every eigenvector to all
orders for slowly varying Jacobi matrices; operator-norm eigenvector matrix).  **Not yet imported by `FormalResearch.lean`.**
Namespace `FormalResearch.JacobiEigenvectors`; plan, dependency DAG and the Layer-4 residual list: `FormalResearch/JacobiEigenvectors/PLAN.md`.

* `Setting/JacobiFamily`: the Jacobi family `J_h`, (D_M), (E_K), (H1)--(H3), parity freezing, mirror and gauge families.
* `Charts/*`: the hypothesis structures (`ChartInputs`): engine interface `LadderChain`, parabolic-cylinder facts, bulk Weber chart, soft-edge chart, transfer coefficients.
* `TheoremA/*`: the comparison vectors and the Prop-valued statements of thm:A, prop:tha-W/W2, lem:tha-win/M/count, prop:l2jets, thm:smo-spec; `GeometryStatements` (lem:tha-geom (a)--(d) per block); `EigenvalueStatements` (Step 0 of app_thmA, cor:eigen (a)--(d)).
* `TheoremB/*`: the comparison matrices and the statements of prop:tha-splice, lem:tha-Mflat, lem:tha-collar, prop:thb-inputs, thm:B, cor:thb-Dm.

The engine is currently `FormalResearch.JE` (to become `FormalResearch.JacobiEigenvectors.Engine`); `FormalResearch.JB` (Theorem B reduction) is to be folded into `TheoremB/` later.
No placeholder proofs and no added axioms: statements are `def ... : Prop`, to be proved later.
-/
