module

public import DLMFMathlib.Analysis.ODE.SturmComparison
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenFinite
public import DLMF.ParabolicCylinder.Basic.Wronskians
public import DLMF.ParabolicCylinder.Basic.WeberEquation
public import DLMF.Confluent.ParabolicCylinder.WronskiansAndConnections
public import DLMF.ParabolicCylinder.ElementaryPropertiesCore

/-!
# Smoke test for the vendored lean-DLMF closures

Re-states the headline results of the closures vendored under `ThirdParty/lean-dlmf/` (see its
`NOTICE.md`) and pins their axioms. Not imported by `FormalResearch.lean`; build with
`lake build FormalResearch.Special.VendoredDlmfSmoke`.

* Liouville–Green and Sturm (Mathlib-only closure): `ODE.sturm_comparison`, and the finite-endpoint
  oscillatory Liouville–Green expansion `LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint`.
* Parabolic cylinder functions (DLMF §12.2, §12.7): the Wronskian `parabolicCylinderV_wronskian`
  (DLMF 12.2.10), Weber's equation for `U` and `V` (DLMF 12.2.2), the Hermite specialisation
  `parabolicCylinderD_nat` (DLMF 12.7.2), and the local Hermite recurrence `hermite_add_two` that
  replaces a TauCeti lemma (a `-- PATCH` in `WeberEquation.lean`).
* Connection formulas and recurrences (DLMF 12.2.15, 12.2.16, 12.8.6, 12.8.7; `WronskiansAndConnections.lean`),
  and reality of `U` and `V` for real parameter and argument (`ElementaryPropertiesCore.lean`, extracted from
  `ElementaryProperties.lean`).
-/

@[expose] public section

#check @ODE.sturm_comparison
#check @LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint
#check @DLMF.Confluent.parabolicCylinderV_wronskian
#check @DLMF.Confluent.isWeberSolution_parabolicCylinderU
#check @DLMF.Confluent.isWeberSolution_parabolicCylinderV
#check @DLMF.Confluent.parabolicCylinderD_nat
#check @DLMF.Confluent.hermite_add_two
#check @DLMF.Confluent.parabolicCylinderU_neg_eq
#check @DLMF.Confluent.parabolicCylinderV_neg_eq
#check @DLMF.Confluent.parabolicCylinderV_recurrence_add
#check @DLMF.Confluent.parabolicCylinderV_recurrence_sub
#check @DLMF.Confluent.parabolicCylinderU_real
#check @DLMF.Confluent.parabolicCylinderV_real

/-- info: 'ODE.sturm_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.sturm_comparison

/-- info: 'LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint

/-- info: 'DLMF.Confluent.parabolicCylinderV_wronskian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderV_wronskian

/-- info: 'DLMF.Confluent.isWeberSolution_parabolicCylinderU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.isWeberSolution_parabolicCylinderU

/-- info: 'DLMF.Confluent.isWeberSolution_parabolicCylinderV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.isWeberSolution_parabolicCylinderV

/-- info: 'DLMF.Confluent.parabolicCylinderD_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderD_nat

/-- info: 'DLMF.Confluent.hermite_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.hermite_add_two

/-- info: 'DLMF.Confluent.parabolicCylinderU_neg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderU_neg_eq

/-- info: 'DLMF.Confluent.parabolicCylinderV_neg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderV_neg_eq

/-- info: 'DLMF.Confluent.parabolicCylinderV_recurrence_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderV_recurrence_add

/-- info: 'DLMF.Confluent.parabolicCylinderV_recurrence_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderV_recurrence_sub

/-- info: 'DLMF.Confluent.parabolicCylinderU_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderU_real

/-- info: 'DLMF.Confluent.parabolicCylinderV_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLMF.Confluent.parabolicCylinderV_real
