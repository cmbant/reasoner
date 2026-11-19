module

public import DLMFMathlib.Analysis.ODE.SturmComparison
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenFinite

/-!
# Smoke test for the vendored lean-DLMF Liouville–Green and Sturm closures

Re-states the headline results of the Mathlib-only closures vendored under
`ThirdParty/lean-dlmf/` (see its `NOTICE.md`) and pins their axioms. Not imported by
`FormalResearch.lean`; build with `lake build FormalResearch.Special.VendoredDlmfSmoke`.

Not covered here: the parabolic-cylinder Wronskian `parabolicCylinderV_wronskian`
(`DLMF.ParabolicCylinder.Basic.Wronskians`), whose closure is blocked on a TauCeti module
(see `NOTICE.md`).
-/

@[expose] public section

#check @ODE.sturm_comparison
#check @LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint

/-- info: 'ODE.sturm_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.sturm_comparison

/-- info: 'LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint
