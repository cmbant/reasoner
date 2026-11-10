module

public import FormalResearch.GurvitsBarnum.Basic
public import FormalResearch.ConvexGeometry.ClosedHull
public import FormalResearch.GurvitsBarnum.Closed
public import FormalResearch.GurvitsBarnum.Separation
public import FormalResearch.GurvitsBarnum.Choi
public import FormalResearch.GurvitsBarnum.BlockBound
public import FormalResearch.GurvitsBarnum.Witness
public import FormalResearch.GurvitsBarnum.ContractionBase
public import FormalResearch.GurvitsBarnum.ContractionUnitary
public import FormalResearch.GurvitsBarnum.ContractionPolar
public import FormalResearch.GurvitsBarnum.Contraction
public import FormalResearch.GurvitsBarnum.Ball

/-!
# The Gurvits–Barnum separable ball

**Theorem** (`FormalResearch.GurvitsBarnum.gurvits_barnum`; L. Gurvits and H. Barnum, *Largest
separable balls around the maximally mixed bipartite quantum state*, Phys. Rev. A 66, 062311 (2002)).
For finite index types `ι`, `κ` and a Hermitian `Δ : Matrix (ι × κ) (ι × κ) ℂ` with
`∑ ‖Δ p q‖² ≤ 1` (Hilbert–Schmidt norm at most `1`), the matrix `1 + Δ` is separable, i.e. a finite
sum of product rank-one positive matrices.  Scaled form:
`isSeparable_of_sum_norm_sq_sub_smul_one_le`.  Equivalent witness inequality:
`sum_norm_sq_le_trace_sq_of_blockPositive` (`‖W‖₂ ≤ tr W` for Hermitian block-positive `W`).

**Proof route.**
1. *Block-positive witness duality* (`Basic`, `ClosedHull`, `Closed`, `Separation`): the separable cone
   is a closed convex cone in a finite-dimensional space; a Hermitian non-separable `X` is strictly
   separated from it by a Hermitian block-positive witness `W` with `Re tr (W X) < 0`
   (`exists_blockPositive_separating`).
2. *Choi map normalisation* (`Choi`, `BlockBound`, `Witness`): a block-positive `W` defines a positive
   map `φ_W`; after the congruence by `φ_W(1)^{-1/2}` (applied to `W + ε 1`) it becomes a positive unital
   map, and `Re tr (W (1 + Δ)) ≥ 0` reduces to the block Cauchy–Schwarz inequality with the contraction
   bound for positive unital maps (`Witness.trace_mul_one_add_nonneg`).
3. *Russo–Dye-type contraction* (`ContractionBase`, `ContractionUnitary`, `ContractionPolar`,
   `Contraction`): a positive unital map sends unitaries to contractions (spectral theorem for
   unitaries and Cauchy–Schwarz twice), and an invertible contraction is an average of two unitaries
   (polar decomposition), so positive unital maps are contractive on all contractions (closure for the
   non-invertible case).
4. *Assembly* (`Ball`): double-sum Cauchy–Schwarz turns the Hilbert–Schmidt bound into the contraction
   bound, and contradiction with the witness gives the ball.
-/

@[expose] public section

