import Mathlib
import FormalResearch.GurvitsBarnum.Choi

/-!
# Gurvits–Barnum separable ball: block Cauchy–Schwarz

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002), proof of Theorem 1, chain (7)–(9); plan lemma L4
(module M5).

The contraction bound (plan lemma L3, Russo–Dye for positive unital maps) is a hypothesis
`BlockBound.ContractionBound φ`: for `X` with Frobenius norm at most `c` and all vectors `u`, `w`,
`|⟨u, φ(X) w⟩| ≤ c ‖u‖ ‖w‖`.  Euclidean norms of vectors are the local helper `BlockBound.vnorm`
(`√(∑ ‖u i‖²)`).  Given it, for Hermitian `Δ` of Frobenius norm at most one and a Hermitian-preserving
unital `φ`, `(id ⊗ φ)(1 + Δ)` is positive semidefinite (`BlockBound.idTensor_one_add_posSemidef`).
-/

set_option linter.unusedSectionVars false

namespace FormalResearch.GurvitsBarnum

open Matrix ComplexOrder

noncomputable section

namespace BlockBound

/-- Euclidean norm of a complex vector on a finite index type. -/
def vnorm {α : Type*} [Fintype α] (u : α → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

theorem vnorm_nonneg {α : Type*} [Fintype α] (u : α → ℂ) : 0 ≤ vnorm u := Real.sqrt_nonneg _

theorem vnorm_sq {α : Type*} [Fintype α] (u : α → ℂ) : vnorm u ^ 2 = ∑ i, ‖u i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- The contraction bound for a linear map `φ : M_κ → M_μ` (a consequence of Russo–Dye for positive
unital maps, plan lemma L3): if `∑ ‖X i j‖² ≤ c²` then `‖⟨u, φ(X) w⟩‖ ≤ c ‖u‖ ‖w‖`. -/
def ContractionBound (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ) : Prop :=
  ∀ (X : Matrix κ κ ℂ) (c : ℝ), 0 ≤ c → (∑ i, ∑ j, ‖X i j‖ ^ 2) ≤ c ^ 2 →
    ∀ (u w : μ → ℂ), ‖star u ⬝ᵥ (φ X *ᵥ w)‖ ≤ c * vnorm u * vnorm w

/-- The quadratic form of `(id ⊗ φ) Y` splits into block pairings. -/
theorem star_dotProduct_idTensor (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ)
    (Y : Matrix (ι × κ) (ι × κ) ℂ) (v : ι × μ → ℂ) :
    star v ⬝ᵥ (idTensor φ Y *ᵥ v)
      = ∑ i, ∑ j, star (fun i' => v (i, i')) ⬝ᵥ
          (φ (matBlock Y i j) *ᵥ fun j' => v (j, j')) := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, idTensor_apply, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- The Frobenius mass of the `(i, j)` block, summed over `(i, j)`, is the total Frobenius mass. -/
theorem sum_block_sq (Δ : Matrix (ι × κ) (ι × κ) ℂ) :
    ∑ i, ∑ j, (∑ k, ∑ l, ‖matBlock Δ i j k l‖ ^ 2) = ∑ p, ∑ q, ‖Δ p q‖ ^ 2 := by
  simp only [Fintype.sum_prod_type, matBlock_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- **Block Cauchy–Schwarz** (Gurvits–Barnum, PRA 66, 062311, Thm. 1, chain (7)–(9); plan lemma L4).
For Hermitian `Δ` with `∑ ‖Δ p q‖² ≤ 1` and a Hermitian-preserving unital linear map `φ` satisfying the
contraction bound, `(id ⊗ φ)(1 + Δ)` is positive semidefinite. -/
theorem idTensor_one_add_posSemidef (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ)
    (hφh : ∀ X, φ Xᴴ = (φ X)ᴴ) (hφ1 : φ 1 = 1) (hc : ContractionBound φ)
    (Δ : Matrix (ι × κ) (ι × κ) ℂ) (hΔh : Δ.IsHermitian)
    (hΔ : ∑ p, ∑ q, ‖Δ p q‖ ^ 2 ≤ 1) :
    (idTensor φ (1 + Δ)).PosSemidef := by
  rw [map_add, idTensor_one_of_unital hφ1]
  set H : Matrix (ι × μ) (ι × μ) ℂ := idTensor φ Δ with hH
  have hHh : H.IsHermitian := by
    ext ⟨i, i'⟩ ⟨j, j'⟩
    have hb : matBlock Δ i j = (matBlock Δ j i)ᴴ := by
      ext k l
      simp only [matBlock_apply, conjTranspose_apply]
      exact (hΔh.apply (i, k) (j, l)).symm
    simp only [hH, conjTranspose_apply, idTensor_apply, hb, hφh]
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_one.add hHh) fun v => ?_
  rw [add_mulVec, dotProduct_add, one_mulVec]
  -- the real number `s = ‖v‖²`
  set s : ℝ := ∑ p, ‖v p‖ ^ 2 with hs
  have hvv : star v ⬝ᵥ v = (s : ℂ) := by
    simp only [dotProduct, Pi.star_apply, hs, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  set z : ℂ := star v ⬝ᵥ (H *ᵥ v) with hz
  have hzim : z.im = 0 := hHh.im_star_dotProduct_mulVec_self v
  -- block norms
  set x : ι → ℝ := fun i => vnorm (fun i' => v (i, i')) with hx
  set a : ι → ι → ℝ := fun i j => Real.sqrt (∑ k, ∑ l, ‖matBlock Δ i j k l‖ ^ 2) with ha
  have hxs : ∑ i, x i ^ 2 = s := by
    simp only [hx, vnorm_sq, hs, Fintype.sum_prod_type]
  have ha2 : ∀ i j, a i j ^ 2 = ∑ k, ∑ l, ‖matBlock Δ i j k l‖ ^ 2 := fun i j =>
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hterm : ∀ i j, ‖star (fun i' => v (i, i')) ⬝ᵥ
      (φ (matBlock Δ i j) *ᵥ fun j' => v (j, j'))‖ ≤ a i j * x i * x j := fun i j =>
    hc _ _ (Real.sqrt_nonneg _) (le_of_eq (ha2 i j).symm) _ _
  have hznorm : ‖z‖ ≤ ∑ i, ∑ j, a i j * x i * x j := by
    rw [hz, hH, star_dotProduct_idTensor]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
  -- Cauchy–Schwarz in `(i, j)`
  have hCS : (∑ i, ∑ j, a i j * x i * x j) ^ 2 ≤ s ^ 2 := by
    have h1 : (∑ i, ∑ j, a i j * x i * x j) = ∑ q : ι × ι, a q.1 q.2 * (x q.1 * x q.2) := by
      rw [Fintype.sum_prod_type]
      simp only [mul_assoc]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
      (fun q => a q.1 q.2) (fun q => x q.1 * x q.2)
    have h3 : ∑ q : ι × ι, (a q.1 q.2) ^ 2 ≤ 1 := by
      rw [Fintype.sum_prod_type]
      simp only [ha2]
      rw [sum_block_sq]
      exact hΔ
    have h4 : ∑ q : ι × ι, (x q.1 * x q.2) ^ 2 = s ^ 2 := by
      rw [Fintype.sum_prod_type, ← hxs, sq, Finset.sum_mul_sum]
      simp only [mul_pow]
    rw [h1]
    calc _ ≤ _ := h2
      _ ≤ 1 * s ^ 2 := by
        rw [h4]
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = s ^ 2 := one_mul _
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ i, ∑ j, a i j * x i * x j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (vnorm_nonneg _)) (vnorm_nonneg _)
  have hSs : ∑ i, ∑ j, a i j * x i * x j ≤ s :=
    (pow_le_pow_iff_left₀ hS0 hs0 two_ne_zero).mp hCS
  have hre : -s ≤ z.re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm z).trans (hznorm.trans hSs))).1
    linarith
  rw [hvv]
  rw [Complex.nonneg_iff]
  refine ⟨?_, by simp [hzim]⟩
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

end BlockBound

end

end FormalResearch.GurvitsBarnum

/-- info: 'FormalResearch.GurvitsBarnum.BlockBound.idTensor_one_add_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.BlockBound.idTensor_one_add_posSemidef

