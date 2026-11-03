module

public import FormalResearch.GurvitsBarnum.Closed

/-!
# Separation of a Hermitian non-separable matrix by a block-positive witness (plan lemma D2)

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002); plan lemma D2.

The separable cone is a proper cone (closed by `isClosed_isSeparable`) in the real locally convex space
of matrices.  `ProperCone.hyperplane_separation_point` gives a continuous real functional `f`; it is
represented as `f Y = Re tr (W Y)` (`exists_matrix_of_functional`), and `W` is replaced by its Hermitian
part (which does not change `Re tr (W S)` for Hermitian `S`).
-/

@[expose] public section


namespace FormalResearch.GurvitsBarnum

open Matrix

noncomputable section

section LC

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Matrices over `ℂ` form a locally convex real topological vector space (Pi topology). `LocallyConvexSpace` is a
`Prop`, so this global instance cannot create a diamond. -/
instance instLocallyConvexSpaceMatrix : LocallyConvexSpace ℝ (Matrix m n ℂ) := by
  let := Matrix.normedAddCommGroup (m := m) (n := n) (α := ℂ)
  let := Matrix.normedSpace (m := m) (n := n) (α := ℂ) (R := ℝ)
  exact NormedSpace.toLocallyConvexSpace

end LC

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The separable cone as a proper cone. -/
def sepCone : ProperCone ℝ (Matrix (ι × κ) (ι × κ) ℂ) where
  carrier := {X | IsSeparable X}
  add_mem' := fun hx hy => IsSeparable.add hx hy
  zero_mem' := isSeparable_zero
  smul_mem' := fun c _ hX => hX.smul_nonneg c.2
  isClosed' := isClosed_isSeparable

/-- Every continuous real-linear functional on `n × n` complex matrices is `Y ↦ Re tr (W Y)`. -/
theorem exists_matrix_of_functional {p : Type*} [Fintype p] [DecidableEq p]
    (f : StrongDual ℝ (Matrix p p ℂ)) :
    ∃ W : Matrix p p ℂ, ∀ Y, f Y = (trace (W * Y)).re := by
  refine ⟨Matrix.of fun q r => ⟨f (single r q (1 : ℂ)), -f (single r q Complex.I)⟩, fun Y => ?_⟩
  have hY := matrix_eq_sum_single Y
  suffices h : f (∑ r, ∑ q, single r q (Y r q)) =
      (trace (Matrix.of (fun q r => (⟨f (single r q (1 : ℂ)), -f (single r q Complex.I)⟩ : ℂ)) *
        ∑ r, ∑ q, single r q (Y r q))).re by rwa [← hY] at h
  simp only [map_sum, Finset.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => ?_
  have hs : single r q (Y r q) =
      (Y r q).re • single r q (1 : ℂ) + (Y r q).im • single r q Complex.I := by
    simp only [smul_single, ← single_add]
    congr 1
    apply Complex.ext <;> simp
  rw [hs, map_add, map_smul, map_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    trace_add, trace_smul, trace_smul, trace_mul_single, trace_mul_single]
  simp [Complex.mul_re]

/-- For Hermitian `S`, `Re tr (Wᴴ S) = Re tr (W S)`. -/
theorem re_trace_conjTranspose_mul {p : Type*} [Fintype p] (W S : Matrix p p ℂ)
    (hS : S.IsHermitian) : (trace (Wᴴ * S)).re = (trace (W * S)).re := by
  have : Wᴴ * S = (S * W)ᴴ := by rw [conjTranspose_mul, hS.eq]
  rw [this, trace_conjTranspose, Complex.star_def, Complex.conj_re, trace_mul_comm]

/-- **Plan lemma D2** (separation).  A Hermitian matrix that is not separable is strictly separated
from the separable cone by a Hermitian block-positive witness.  Gurvits–Barnum, PRA 66, 062311 (2002). -/
theorem exists_blockPositive_separating {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.IsHermitian)
    (hns : ¬ IsSeparable X) :
    ∃ W : Matrix (ι × κ) (ι × κ) ℂ, W.IsHermitian ∧ IsBlockPositive W ∧
      (trace (W * X)).re < 0 := by
  obtain ⟨f, hf, hfX⟩ := ProperCone.hyperplane_separation_point
    (sepCone (ι := ι) (κ := κ)) (x₀ := X) hns
  obtain ⟨W, hW⟩ := exists_matrix_of_functional f
  refine ⟨(1 / 2 : ℝ) • (W + Wᴴ), ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    simp
  · rw [isBlockPositive_iff_forall_separable]
    intro S hS
    rw [smul_mul_assoc, trace_smul, add_mul, trace_add, Complex.smul_re,
      Complex.add_re, re_trace_conjTranspose_mul W S hS.isHermitian, ← hW]
    have := hf S hS
    simp only [smul_eq_mul]
    linarith
  · rw [smul_mul_assoc, trace_smul, add_mul, trace_add, Complex.smul_re,
      Complex.add_re, re_trace_conjTranspose_mul W X hX, ← hW]
    simp only [smul_eq_mul]
    linarith

/-- info: 'FormalResearch.GurvitsBarnum.exists_blockPositive_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_blockPositive_separating

end

end FormalResearch.GurvitsBarnum
