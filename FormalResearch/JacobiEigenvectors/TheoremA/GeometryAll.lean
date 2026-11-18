module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryCollision
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryMargins

/-!
# Paper J, Layer 2 (L2.G4): lem:tha-geom assembled

`TheGeometry F K r` (frozen, `GeometryStatements.lean`) is the conjunction of (a) `GeomBulk`, (b) `GeomCollision`,
(c) `GeomMargins`, and the two soft-edge statements (d) `GeomSoft`, `GeomSoftLower`.  Parts (a), (b), (c) are proved
(`HypMorse.geomBulk`, `Collision.geomCollision`, `Margins.geomMargins`).  The soft-edge statements (d) are not yet proved,
so this file proves `TheGeometry` from them; `TheGeometry` itself is open until they are.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open FormalResearch.JacobiEigenvectors.Setting

/-- lem:tha-geom: `TheGeometry` follows from the soft-edge statements (d). -/
theorem theGeometry_of_soft {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (r : ℕ)
    (hs : GeomSoft F K r) (hsl : GeomSoftLower F K r) : TheGeometry F K r :=
  ⟨HypMorse.geomBulk, Collision.geomCollision F K, Margins.geomMargins F K, hs, hsl⟩

end FormalResearch.JacobiEigenvectors.TheoremA

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.theGeometry_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.theGeometry_of_soft
