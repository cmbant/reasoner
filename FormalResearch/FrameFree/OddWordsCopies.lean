import Mathlib
import FormalResearch.FrameFree.OddWordsReal

/-!
# `k` copies: the symmetrizer, product vectors and time reversal (Paper P, `prop:oddwords` (i), (ii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

Slots are `α × γ` (spin `a`, copy `g`), `π : α → κ` the frame-sharing pattern (the paper's words are
`π = id`).  `kronVec γ ψ = ψ^{⊗γ}`, `thetaVec ψ = Θψ = ε ψ̄`, `symmetrizer α γ` the projector onto the
copy-symmetric subspace `Sym^k V` (a real symmetric element of `rPerm`), and `ev A v = ⟨v|A v⟩`.
This file collects the elementary facts used by `OddWordsCompressed`, `OddWordsPolar` and `OddWordsOddIff`:
`symmetrizer` fixes `ψ^{⊗γ}`, `Θ (ψ^{⊗γ}) = (Θψ)^{⊗γ}`, and `⟨Θv|P_σ Θv⟩ = conj ⟨v|P_σ v⟩`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.Twirls

section Basics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expectation `⟨v|A v⟩` in the product basis. -/
def ev (A : OpS ι) (v : (ι → Fin 2) → ℂ) : ℂ := star v ⬝ᵥ (A *ᵥ v)

theorem ev_add (A B : OpS ι) (v : (ι → Fin 2) → ℂ) : ev (A + B) v = ev A v + ev B v := by
  simp [ev, Matrix.add_mulVec, dotProduct_add]

theorem ev_smul (c : ℂ) (A : OpS ι) (v : (ι → Fin 2) → ℂ) : ev (c • A) v = c * ev A v := by
  simp [ev, Matrix.smul_mulVec, dotProduct_smul]

theorem ev_sub (A B : OpS ι) (v : (ι → Fin 2) → ℂ) : ev (A - B) v = ev A v - ev B v := by
  simp [ev, Matrix.sub_mulVec, dotProduct_sub]

theorem ev_zero (v : (ι → Fin 2) → ℂ) : ev (0 : OpS ι) v = 0 := by simp [ev]

theorem ev_sum (A : OpS ι) (v : (ι → Fin 2) → ℂ) :
    ev A v = ∑ x, ∑ y, conj (v x) * (A x y * v y) := by
  simp [ev, Matrix.mulVec, dotProduct, Finset.mul_sum]

theorem conj_ev (A : OpS ι) (v : (ι → Fin 2) → ℂ) : conj (ev A v) = ev Aᴴ v := by
  rw [ev_sum, ev_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [map_mul, Complex.conj_conj, Matrix.conjTranspose_apply, Complex.star_def]
  ring

theorem ev_real_of_herm {A : OpS ι} (h : Aᴴ = A) (v : (ι → Fin 2) → ℂ) : conj (ev A v) = ev A v := by
  rw [conj_ev, h]

theorem permOp_mulVec' (σ : Equiv.Perm ι) (v : (ι → Fin 2) → ℂ) :
    permOp σ *ᵥ v = fun x => v (x ∘ σ) := by
  funext x
  simp [permOp, Matrix.mulVec, dotProduct]

/-- Time reversal on all slots, `Θ v = ε^{⊗ι} v̄`. -/
noncomputable def thetaN (v : (ι → Fin 2) → ℂ) : (ι → Fin 2) → ℂ := epsOp ι *ᵥ (fun x => conj (v x))

theorem ev_conjvec {A : OpS ι} (hA : A.map conj = A) (v : (ι → Fin 2) → ℂ) :
    ev A (fun x => conj (v x)) = conj (ev A v) := by
  rw [ev_sum, ev_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := congrFun (congrFun hA a) b
  simp only [Matrix.map_apply] at this
  simp only [map_mul, Complex.conj_conj, this]

theorem ev_unitary_conj {U A : OpS ι} (hU : Uᴴ * U = 1) (hc : U * A = A * U) (w : (ι → Fin 2) → ℂ) :
    ev A (U *ᵥ w) = ev A w := by
  unfold ev
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

theorem ev_permOp_thetaN (σ : Equiv.Perm ι) (v : (ι → Fin 2) → ℂ) :
    ev (permOp σ) (thetaN v) = conj (ev (permOp σ) v) := by
  rw [thetaN, ev_unitary_conj (epsOp_unitary (ι := ι)) (epsOp_commute_permOp σ),
    ev_conjvec (permOp_map_conj σ)]

end Basics

section Copies

variable {α γ κ : Type*} [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ] [Fintype κ]
  [DecidableEq κ]

/-- The product vector `ψ^{⊗γ}` on the slots `α × γ`. -/
def kronVec (γ : Type*) [Fintype γ] (ψ : (α → Fin 2) → ℂ) : (α × γ → Fin 2) → ℂ :=
  fun x => ∏ g, ψ (fun a => x (a, g))

/-- Permutation of the copies, applied to every spin simultaneously. -/
def copyPerm (c : Equiv.Perm γ) : Equiv.Perm (α × γ) := Equiv.prodCongr (Equiv.refl α) c

/-- The projector onto the copy-symmetric subspace `Sym^k V`. -/
noncomputable def symmetrizer (α γ : Type*) [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ] :
    OpS (α × γ) :=
  ((Fintype.card (Equiv.Perm γ) : ℝ)⁻¹) • ∑ c : Equiv.Perm γ, permOp (copyPerm (α := α) c)

theorem permOp_copyPerm_kronVec (c : Equiv.Perm γ) (ψ : (α → Fin 2) → ℂ) :
    permOp (copyPerm (α := α) c) *ᵥ kronVec γ ψ = kronVec γ ψ := by
  rw [permOp_mulVec']
  funext x
  simp only [kronVec, copyPerm, Function.comp_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq]
  exact Equiv.prod_comp c (fun g => ψ (fun a => x (a, g)))

theorem symmetrizer_mulVec_kronVec (ψ : (α → Fin 2) → ℂ) :
    symmetrizer α γ *ᵥ kronVec γ ψ = kronVec γ ψ := by
  rw [symmetrizer, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [permOp_copyPerm_kronVec, Finset.sum_const, Finset.card_univ]
  funext x
  have hN : (Fintype.card (Equiv.Perm γ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Pi.smul_apply, nsmul_eq_mul, Complex.real_smul, Pi.mul_apply, Pi.natCast_apply]
  push_cast
  field_simp

theorem thetaN_kronVec (ψ : (α → Fin 2) → ℂ) :
    thetaN (kronVec γ ψ) = kronVec γ (thetaN ψ) := by
  funext x
  unfold thetaN
  rw [epsOp_prod]
  simp only [Matrix.mulVec, dotProduct, kronPow, Matrix.of_apply, kronVec, map_prod]
  rw [← sum_copies (γ := γ) (fun g b => epsOp α (fun a => x (a, g)) b * conj (ψ b))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

theorem symmetrizer_mem {P : α × γ → κ} (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q) :
    symmetrizer α γ ∈ rPerm P :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨copyPerm c, hP c, rfl⟩)

theorem copyPerm_inv (c : Equiv.Perm γ) : (copyPerm (α := α) c)⁻¹ = copyPerm c⁻¹ := by
  ext q <;> simp [copyPerm]

theorem symmetrizer_transpose : (symmetrizer α γ)ᵀ = symmetrizer α γ := by
  rw [symmetrizer, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  simp only [permOp_transpose', copyPerm_inv]
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm γ)) (fun c => permOp (copyPerm (α := α) c))

end Copies

end FormalResearch.FrameFree.OddWords
