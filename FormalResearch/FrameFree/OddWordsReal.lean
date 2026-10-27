import Mathlib
import FormalResearch.FrameFree.TwirlsOdd

/-!
# Real permutation spans on a general slot set (Paper P, `prop:oddwords` (i), (ii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`TwirlsOdd` works on `Fin n`; the `k`-copy statements need slots `α × γ`.  This file restates, for an
arbitrary finite slot type `ι` with block pattern `π : ι → κ`, the elementary facts about the real span
`rPerm π` of the block-preserving slot permutations and its antisymmetric part `sSkew π`
(real, closed under transposition and products, `X - Xᵀ ∈ sSkew π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.Twirls

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (π : ι → κ)

/-- Real span of the block-preserving slot permutations. -/
noncomputable def rPerm : Submodule ℝ (OpS ι) :=
  Submodule.span ℝ {M | ∃ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) ∧ M = permOp σ}

/-- Real span of `P_σ - P_σ⁻¹` over block-preserving `σ`. -/
noncomputable def sSkew : Submodule ℝ (OpS ι) :=
  Submodule.span ℝ {M | ∃ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) ∧ M = permOp σ - permOp σ⁻¹}

variable {π}

theorem permOp_transpose' (σ : Equiv.Perm ι) : (permOp σ)ᵀ = permOp σ⁻¹ := by
  ext x y
  have h := congrFun (congrFun (permOp_conjTranspose σ) x) y
  have h2 := congrFun (congrFun (permOp_map_conj σ) y) x
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def] at h h2
  simp only [Matrix.transpose_apply]
  rw [← h, h2]

theorem inv_block' (σ : Equiv.Perm ι) (hσ : ∀ i, π (σ i) = π i) (i : ι) : π (σ⁻¹ i) = π i := by
  have := hσ (σ⁻¹ i)
  simpa using this.symm

theorem rPerm_map_conj {X : OpS ι} (hX : X ∈ rPerm π) : X.map conj = X := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, -, rfl⟩ := hx; exact permOp_map_conj σ
  | zero => ext x y; simp
  | add x y _ _ hx hy =>
    ext a b
    have h1 := congrFun (congrFun hx a) b
    have h2 := congrFun (congrFun hy a) b
    simp only [Matrix.map_apply, Matrix.add_apply, map_add] at h1 h2 ⊢
    rw [h1, h2]
  | smul r x _ hx =>
    ext a b
    have h1 := congrFun (congrFun hx a) b
    simp only [Matrix.map_apply] at h1
    simp only [Matrix.map_apply, Matrix.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, h1]

theorem rPerm_transpose {X : OpS ι} (hX : X ∈ rPerm π) : Xᵀ ∈ rPerm π := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [permOp_transpose']
    exact Submodule.subset_span ⟨σ⁻¹, inv_block' σ hσ, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.transpose_add]; exact add_mem hx hy
  | smul r x _ hx => rw [Matrix.transpose_smul]; exact Submodule.smul_mem _ r hx

theorem rPerm_mul {X Y : OpS ι} (hX : X ∈ rPerm π) (hY : Y ∈ rPerm π) : X * Y ∈ rPerm π := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨τ, hτ, rfl⟩ := hy
      rw [permOp_mul]
      exact Submodule.subset_span ⟨σ * τ, fun i => by rw [Equiv.Perm.mul_apply, hσ, hτ], rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ r ha
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.add_mul]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ r ha

theorem rPerm_sub_transpose {X : OpS ι} (hX : X ∈ rPerm π) : X - Xᵀ ∈ sSkew π := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [permOp_transpose']
    exact Submodule.subset_span ⟨σ, hσ, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have : x + y - (x + y)ᵀ = (x - xᵀ) + (y - yᵀ) := by rw [Matrix.transpose_add]; abel
    rw [this]; exact add_mem hx hy
  | smul r x _ hx =>
    have : r • x - (r • x)ᵀ = r • (x - xᵀ) := by rw [Matrix.transpose_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ r hx

theorem sSkew_le_rPerm : sSkew π ≤ rPerm π := by
  refine Submodule.span_le.2 ?_
  rintro M ⟨σ, hσ, rfl⟩
  exact sub_mem (Submodule.subset_span ⟨σ, hσ, rfl⟩) (Submodule.subset_span ⟨σ⁻¹, inv_block' σ hσ, rfl⟩)

end FormalResearch.FrameFree.OddWords
