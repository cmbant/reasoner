import FormalResearch.QID.D4DoublyStochasticCertificate

namespace FormalResearch.QID

/-!
# Exact Type-D4 rational dual certificate

The source verification log for `QI-D/code/certify_ds_strict_D4.py` records an
exact LP dual with fourteen active coweight-orbit inequalities. Every active
multiplier is `1/6`, every active inequality has dominant bound `1/2`, the
weighted outer products sum to the exceptional facet normal `F`, and the dual
objective is `7/6`.

This module checks those finite rational data exactly. As in the primal
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

/-- Number of fundamental-coweight index pairs `(k,j)` for which a printed
`(u,v)` dual pair belongs to `orbit(ω_k) × orbit(ω_j)` and has bound `1/2`.
This uses only computable `Finset.filter` operations. -/
def d4DualPairMatchCount (uv : D4Vec × D4Vec) : Nat :=
  (((Finset.univ : Finset D4Fin).product (Finset.univ : Finset D4Fin)).filter
    (fun kj => decide (
      uv.1 ∈ d4OmegaOrbit kj.1 ∧
      uv.2 ∈ d4OmegaOrbit kj.2 ∧
      d4CoweightBound kj.1 kj.2 = (1 : ℚ) / 2))).card

/-- A printed dual pair is valid when at least one coweight-index pair realizes
it as an active finite constraint with bound `1/2`. -/
def d4DualPairValid (uv : D4Vec × D4Vec) : Bool :=
  decide (0 < d4DualPairMatchCount uv)

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
