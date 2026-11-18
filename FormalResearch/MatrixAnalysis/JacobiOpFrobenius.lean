module

public import FormalResearch.MatrixAnalysis.JacobiOpPolar
public import FormalResearch.MatrixAnalysis.MaskedFrobenius

/-!
# Jacobi operator package: polar repair in the Frobenius norm

Paper J, `lem:thb-polar`, Frobenius clause: for `U` orthogonal and `G` invertible (in particular
`‖G - U‖ < 1`), the polar factor `Q` of `G` satisfies `‖G - Q‖_F ≤ ‖G - U‖_F` and
`‖Q - U‖_F ≤ 2 ‖G - U‖_F`.  The Frobenius norm is `√(frobSq ·)` of `MaskedFrobenius`, which is
Mathlib's Frobenius norm.

The proof does not use Hoffman–Wielandt (which the paper cites): in an eigenbasis `e_j` of the positive
root `R = (GᵀG)^{1/2}` with eigenvalues `ρ_j ≥ 0` one has `‖(G - Q) e_j‖ = |ρ_j - 1|` while
`‖(G - V) e_j‖ ≥ |‖ρ_j Q e_j‖ - ‖V e_j‖| = |ρ_j - 1|` for every isometry `V`, and the Hilbert–Schmidt sum
`∑ ‖A b_i‖² = trace (A^* A)` does not depend on the orthonormal basis.  So the Frobenius statement is
termwise and holds for every isometry `V` in place of `U`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open FormalResearch.Racah Matrix

section Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Hilbert–Schmidt sum `∑ ‖A b_i‖²` is `trace (A^* A)`, hence independent of the orthonormal basis. -/
lemma jop_sumsq_eq_trace (A : V →ₗ[ℝ] V) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    ∑ i, ‖A (b i)‖ ^ 2 = (LinearMap.adjoint A ∘ₗ A).trace ℝ V := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma jop_sumsq_basis_indep (A : V →ₗ[ℝ] V) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V) :
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ j, ‖A (b' j)‖ ^ 2 := by
  rw [jop_sumsq_eq_trace A b, jop_sumsq_eq_trace A b']

/-- **Hilbert–Schmidt (Frobenius) nearest-isometry property of the polar factor.**  For injective `T`
and every linear isometry `V'`, in any orthonormal basis `b`:
`∑ ‖(T - polarFactor T) b_i‖² ≤ ∑ ‖(T - V') b_i‖²`. -/
theorem jop_frobenius_polarFactor (T V' : V →ₗ[ℝ] V) (hT : Function.Injective T)
    (hV' : ∀ x, ‖V' x‖ = ‖x‖) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    ∑ i, ‖(T - Polar.polarFactor T hT) (b i)‖ ^ 2 ≤ ∑ i, ‖(T - V') (b i)‖ ^ 2 := by
  have hR := Polar.polarRoot_pos T
  have hs := hR.isSymmetric
  set N := Module.finrank ℝ V with hNdef
  set e := hs.eigenvectorBasis (rfl : Module.finrank ℝ V = N) with he
  rw [jop_sumsq_basis_indep _ b e, jop_sumsq_basis_indep _ b e]
  refine Finset.sum_le_sum fun j _ => ?_
  have hej : ‖e j‖ = 1 := e.orthonormal.1 j
  have hRe : Polar.polarRoot T (e j) = (hs.eigenvalues rfl j) • e j := by
    exact hs.apply_eigenvectorBasis (rfl : Module.finrank ℝ V = N) j
  have hρ : 0 ≤ hs.eigenvalues rfl j := hR.nonneg_eigenvalues rfl j
  set ρ := hs.eigenvalues (rfl : Module.finrank ℝ V = N) j
  have hTe : T (e j) = ρ • Polar.polarFactor T hT (e j) := by
    rw [← Polar.polarFactor_root T hT, hRe, map_smul]
  have hQe : ‖Polar.polarFactor T hT (e j)‖ = 1 := by
    rw [Spectral.norm_polarFactor, hej]
  have h1 : ‖(T - Polar.polarFactor T hT) (e j)‖ ^ 2 = (ρ - 1) ^ 2 := by
    have hsm : ρ • Polar.polarFactor T hT (e j) - Polar.polarFactor T hT (e j) =
        (ρ - 1) • Polar.polarFactor T hT (e j) := by rw [sub_smul, one_smul]
    rw [LinearMap.sub_apply, hTe, hsm, norm_smul, hQe, Real.norm_eq_abs, mul_one, sq_abs]
  have h2 : (ρ - 1) ^ 2 ≤ ‖(T - V') (e j)‖ ^ 2 := by
    have h3 := abs_norm_sub_norm_le (T (e j)) (V' (e j))
    rw [hTe, norm_smul, hQe, hV', hej, Real.norm_eq_abs, abs_of_nonneg hρ, mul_one] at h3
    rw [LinearMap.sub_apply, hTe]
    calc (ρ - 1) ^ 2 = |ρ - 1| ^ 2 := (sq_abs _).symm
      _ ≤ _ := by gcongr
  rw [h1]; exact h2

end Operator

section MatrixForm

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma jop_frobSq_eq_sum (M : Matrix n n ℝ) :
    frobSq M = ∑ j, ‖toEuclideanLin M (EuclideanSpace.basisFun n ℝ j)‖ ^ 2 := by
  unfold frobSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toLpLin_apply, sq_abs]

open scoped Matrix.Norms.Frobenius in
lemma jop_sqrt_frobSq_triangle (A B C : Matrix n n ℝ) :
    √(frobSq (A - C)) ≤ √(frobSq (A - B)) + √(frobSq (B - C)) := by
  rw [← frobenius_norm_eq_sqrt_frobSq, ← frobenius_norm_eq_sqrt_frobSq,
    ← frobenius_norm_eq_sqrt_frobSq]
  calc ‖A - C‖ = ‖(A - B) + (B - C)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

omit [DecidableEq n] in
lemma jop_frobSq_neg_sub (A B : Matrix n n ℝ) : frobSq (A - B) = frobSq (B - A) := by
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.sub_apply]; ring

/-- **Polar repair, Frobenius norm** (Paper J `lem:thb-polar`).  For an orthogonal `U` and an injective
(invertible) `G`, the polar factor `Q = jop_polarMatrix G` satisfies `‖G - Q‖_F ≤ ‖G - U‖_F` and
`‖Q - U‖_F ≤ 2‖G - U‖_F`, with `‖M‖_F = √(frobSq M)`.  This needs only invertibility of `G`
(implied by `‖G - U‖ < 1`, see `jop_polar_repair_frobenius_of_close`); it is proved directly
(`jop_frobenius_polarFactor`), not by Hoffman–Wielandt. -/
theorem jop_polar_repair_frobenius (G U : Matrix n n ℝ) (hU : Uᵀ * U = 1)
    (hinj : Function.Injective (toEuclideanLin G)) :
    √(frobSq (G - jop_polarMatrix G hinj)) ≤ √(frobSq (G - U)) ∧
      √(frobSq (jop_polarMatrix G hinj - U)) ≤ 2 * √(frobSq (G - U)) := by
  have hkey : frobSq (G - jop_polarMatrix G hinj) ≤ frobSq (G - U) := by
    rw [jop_frobSq_eq_sum, jop_frobSq_eq_sum]
    have := jop_frobenius_polarFactor (toEuclideanLin G) (toEuclideanLin U) hinj
      (jop_norm_orth hU) (EuclideanSpace.basisFun n ℝ)
    simpa [map_sub, jop_toEuclideanLin_polarMatrix] using this
  have h1 : √(frobSq (G - jop_polarMatrix G hinj)) ≤ √(frobSq (G - U)) :=
    Real.sqrt_le_sqrt hkey
  refine ⟨h1, ?_⟩
  have h2 := jop_sqrt_frobSq_triangle (jop_polarMatrix G hinj) G U
  rw [jop_frobSq_neg_sub (jop_polarMatrix G hinj) G] at h2
  linarith

section Close

open scoped Matrix.Norms.L2Operator

/-- The Frobenius clause of `lem:thb-polar` under the paper's hypothesis `‖G - U‖ < 1` (spectral norm). -/
theorem jop_polar_repair_frobenius_of_close (G U : Matrix n n ℝ) (hU : Uᵀ * U = 1)
    (hGU : ‖G - U‖ < 1) :
    √(frobSq (G - jop_polarMatrix G (jop_injective_of_close hU hGU))) ≤ √(frobSq (G - U)) ∧
      √(frobSq (jop_polarMatrix G (jop_injective_of_close hU hGU) - U)) ≤ 2 * √(frobSq (G - U)) :=
  jop_polar_repair_frobenius G U hU _

end Close

/-- info: 'FormalResearch.MatrixAnalysis.jop_frobenius_polarFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_frobenius_polarFactor

/-- info: 'FormalResearch.MatrixAnalysis.jop_polar_repair_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_polar_repair_frobenius

/-- info: 'FormalResearch.MatrixAnalysis.jop_polar_repair_frobenius_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_polar_repair_frobenius_of_close

end MatrixForm

end FormalResearch.MatrixAnalysis
