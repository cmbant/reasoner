import FormalResearch.QID.D4DoublyStochasticCertificate

namespace FormalResearch.QID

/-!
# Exact Type-D4 rational dual certificate

The source verification log for `QI-D/code/certify_ds_strict_D4.py` records an
exact LP dual with fourteen active coweight-orbit inequalities.  Every active
multiplier is `1/6`, every active inequality has dominant bound `1/2`, the
weighted outer products sum to the exceptional facet normal `F`, and the dual
objective is `7/6`.

This module checks those finite rational data exactly.  As in the primal
certificate module, the general theorem identifying the coweight inequalities
with `DS(W(D₄))` is an external semantic layer rather than being silently
reintroduced here.
-/

/-- The fourteen active `(u,v)` pairs printed by the exact rational dual log. -/
def d4DualPairs : List (D4Vec × D4Vec) :=
  [
    ((![-1, 0, 0, 0] : D4Vec),
      (![1/2, -1/2, 1/2, 1/2] : D4Vec)),
    ((![0, -1, 0, 0] : D4Vec),
      (![-1/2, 1/2, 1/2, 1/2] : D4Vec)),
    ((![-1, 0, 0, 0] : D4Vec),
      (![1/2, -1/2, -1/2, 1/2] : D4Vec)),
    ((![0, -1, 0, 0] : D4Vec),
      (![-1/2, 1/2, -1/2, 1/2] : D4Vec)),
    ((![-1/2, 1/2, -1/2, -1/2] : D4Vec),
      (![1, 0, 0, 0] : D4Vec)),
    ((![-1/2, 1/2, 1/2, 1/2] : D4Vec),
      (![0, -1, 0, 0] : D4Vec)),
    ((![-1/2, -1/2, -1/2, 1/2] : D4Vec),
      (![1/2, 1/2, 1/2, 1/2] : D4Vec)),
    ((![-1/2, 1/2, -1/2, -1/2] : D4Vec),
      (![1/2, -1/2, 1/2, -1/2] : D4Vec)),
    ((![-1/2, 1/2, 1/2, 1/2] : D4Vec),
      (![1/2, -1/2, -1/2, 1/2] : D4Vec)),
    ((![-1/2, 1/2, -1/2, 1/2] : D4Vec),
      (![1, 0, 0, 0] : D4Vec)),
    ((![-1/2, 1/2, 1/2, -1/2] : D4Vec),
      (![0, -1, 0, 0] : D4Vec)),
    ((![-1/2, -1/2, 1/2, 1/2] : D4Vec),
      (![-1/2, -1/2, -1/2, 1/2] : D4Vec)),
    ((![-1/2, 1/2, -1/2, 1/2] : D4Vec),
      (![1/2, -1/2, 1/2, 1/2] : D4Vec)),
    ((![-1/2, 1/2, 1/2, -1/2] : D4Vec),
      (![1/2, -1/2, -1/2, -1/2] : D4Vec))
  ]

/-- The dual uses fourteen active constraints. -/
theorem d4DualPairs_length : d4DualPairs.length = 14 := by
  native_decide

/-- Weighted sum of the fourteen rank-one constraint normals. -/
def d4DualMatrix : Matrix D4Fin D4Fin ℚ :=
  fun i j =>
    (d4DualPairs.map (fun uv => (1/6 : ℚ) * uv.1 i * uv.2 j)).sum

/-- Exact matrix identity required by the LP dual certificate. -/
theorem d4DualMatrix_eq_facetNormal : d4DualMatrix = d4FacetNormal := by
  native_decide

/-- Every active constraint has coefficient `1/6` and bound `1/2`. -/
def d4DualObjective : ℚ :=
  (d4DualPairs.map (fun _ => (1/6 : ℚ) * (1/2 : ℚ))).sum

/-- Exact dual objective `14 * (1/6) * (1/2) = 7/6`. -/
theorem d4DualObjective_value : d4DualObjective = 7 / 6 := by
  native_decide

/-- Check that a printed dual pair is an actual pair of coweight-orbit vectors
for some fundamental-coweight indices whose dominance bound is `1/2`. -/
def d4DualPairValid (uv : D4Vec × D4Vec) : Bool :=
  (Finset.univ : Finset D4Fin).toList.any (fun k =>
    (Finset.univ : Finset D4Fin).toList.any (fun j =>
      decide (
        uv.1 ∈ d4OmegaOrbit k ∧
        uv.2 ∈ d4OmegaOrbit j ∧
        d4CoweightBound k j = (1 : ℚ) / 2)))

/-- All fourteen active dual pairs belong to the finite constraint family. -/
def d4DualPairsValid : Bool :=
  d4DualPairs.all d4DualPairValid

theorem d4DualPairs_valid : d4DualPairsValid = true := by
  native_decide

/-- Bundled exact rational dual data: the printed fourteen active constraints
are admissible, their weighted normal is exactly `F`, and their objective is
exactly `7/6`. -/
theorem d4ExactDualCertificate :
    d4DualPairsValid = true ∧
    d4DualMatrix = d4FacetNormal ∧
    d4DualObjective = 7 / 6 := by
  exact ⟨d4DualPairs_valid, d4DualMatrix_eq_facetNormal, d4DualObjective_value⟩

end FormalResearch.QID
