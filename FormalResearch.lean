module

public import FormalResearch.Analysis
public import FormalResearch.Asymptotics
public import FormalResearch.Complex
public import FormalResearch.ConvexGeometry
public import FormalResearch.MatrixAnalysis
public import FormalResearch.NQubit

/-!
# FormalResearch shared libraries root

Imports only the general-purpose shared libraries (`Analysis`, `Asymptotics`, `Complex`,
`ConvexGeometry`, `MatrixAnalysis`, `NQubit`) so the default root build stays fast and
memory-safe.

Individual papers and research programmes build and verify through their own top-level
umbrella modules (`FormalResearch.ModularBootstrap`, `FormalResearch.SignUncertainty`,
`FormalResearch.TwoEdgeBootstrap`, `FormalResearch.CohnElkies`,
`FormalResearch.JacobiEigenvectors`, `FormalResearch.PPTThreeQubit`,
`FormalResearch.FreeFermion`, `FormalResearch.Wigner`, `FormalResearch.Special`, etc.).
-/

@[expose] public section
