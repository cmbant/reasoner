import Mathlib
import FormalResearch.FrameFree.HelstromTwirl
import FormalResearch.QIB.BlockDecomp

/-!
# The twirl in isotypic coordinates (`lem:blockdecomp`, first formula)

Namespace `FormalResearch.QIB`.  Claim class: **proved under explicit hypothesis**
(`IsotypicInvariants`, see `BlockDecomp.lean`); no Haar measure.

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, Lemma `lem:blockdecomp`:
`Ω_x = ⊕_λ (I_{V_λ}/dim V_λ) ⊗ τ_λ^x`.

A *twirl* of `ρ` is a matrix `Z` commuting with `G` that lies in every closed convex set containing the
orbit `{U ρ U†}` (the Haar-free notion of `FrameFree.Helstrom.twirl_exists`, which gives existence for a
multiplicatively closed set of unitaries).  `twirl_blockForm` shows that, under the isotypic
hypothesis, every twirl of `ρ` equals `⊕_λ I ⊗ (Tr_{A λ} ρ_λλ)/|A λ|`; for `ρ = |v⟩⟨v|` the multiplicity
block is `tau v λ` (`ptrA_vecMulVec`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

namespace FormalResearch.QIB

section Twirl

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- Partial trace over the carrier `A λ` of the `(λ,λ)` diagonal block of `ρ`. -/
def ptrA (ρ : Matrix (Idx A B) (Idx A B) ℂ) (l : Λ) : Matrix (B l) (B l) ℂ :=
  Matrix.of fun b b' => ∑ α, ρ ⟨l, (α, b)⟩ ⟨l, (α, b')⟩

theorem ptrA_vecMulVec (v : Idx A B → ℂ) (l : Λ) :
    ptrA (Matrix.vecMulVec v (star v)) l = tau v l := by
  ext b b'
  simp [ptrA, tau_apply, Matrix.vecMulVec_apply]

theorem ptrA_blockOp (X : ∀ l, Matrix (B l) (B l) ℂ) (l : Λ) :
    ptrA (blockOp A X) l = (Fintype.card (A l) : ℂ) • X l := by
  ext b b'
  simp [ptrA, blockOp_apply_same]

theorem trace_blockOp_mul (Y : ∀ l, Matrix (B l) (B l) ℂ) (M : Matrix (Idx A B) (Idx A B) ℂ) :
    (blockOp A Y * M).trace = ∑ l, (Y l * ptrA M l).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ptrA, Matrix.of_apply]
  have : ∀ (α : A l) (b : B l),
      ∑ l' : Λ, ∑ α' : A l', ∑ b' : B l', blockOp A Y ⟨l, (α, b)⟩ ⟨l', (α', b')⟩ * M ⟨l', (α', b')⟩ ⟨l, (α, b)⟩
        = ∑ b' : B l, Y l b b' * M ⟨l, (α, b')⟩ ⟨l, (α, b)⟩ := by
    intro α b
    rw [Finset.sum_eq_single l]
    · simp only [blockOp_apply_same, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    · intro l' _ hl'
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b' _ => ?_
      rw [blockOp_apply_ne _ (Ne.symm hl'), zero_mul]
    · simp
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← Finset.mul_sum]

/-- **`lem:blockdecomp`, first formula.**  Under the isotypic hypothesis every twirl `Z` of `ρ` is
`⊕_λ (I/|A λ|) ⊗ Tr_{A λ} ρ_λλ`, i.e. `⊕_λ I ⊗ (|A λ|⁻¹ • ptrA ρ λ)`. -/
theorem twirl_blockForm [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (hU : ∀ U ∈ G, Uᴴ * U = 1) (ρ Z : Matrix (Idx A B) (Idx A B) ℂ)
    (hZ : ∀ C : Set (Matrix (Idx A B) (Idx A B) ℂ), IsClosed C → Convex ℝ C →
      (∀ U ∈ G, U * ρ * Uᴴ ∈ C) → Z ∈ C)
    (hZc : ∀ U ∈ G, U * Z = Z * U) :
    Z = blockOp A (fun l => ((Fintype.card (A l) : ℂ)⁻¹) • ptrA ρ l) := by
  -- `Tr(S Z) = Tr(S ρ)` for every invariant `S`
  have key : ∀ S : Matrix (Idx A B) (Idx A B) ℂ, (∀ U ∈ G, U * S = S * U) →
      (S * Z).trace = (S * ρ).trace := by
    intro S hS
    have := hZ {M | (S * M).trace = (S * ρ).trace} ?_ ?_ ?_
    · exact this
    · exact isClosed_eq (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))
        continuous_const
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
        Matrix.trace_smul, hx, hy, ← add_smul]
      simp only [Complex.real_smul, ← add_mul, ← Complex.ofReal_add, hab]
      simp
    · intro U hUG
      simp only [Set.mem_ofPred_eq]
      have h1 : S * (U * ρ * Uᴴ) = U * (S * ρ) * Uᴴ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hS U hUG, Matrix.mul_assoc, Matrix.mul_assoc]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.trace_mul_cycle, hU U hUG, Matrix.one_mul]
  obtain ⟨X, rfl⟩ := (hG Z).1 hZc
  congr 1
  funext l
  -- test against `Y` supported at sector `l`
  have hX : ∀ Y : Matrix (B l) (B l) ℂ,
      (Fintype.card (A l) : ℂ) * (Y * X l).trace = (Y * ptrA ρ l).trace := by
    intro Y
    set Ys : ∀ l', Matrix (B l') (B l') ℂ := Function.update (fun l' => 0) l Y with hYs
    have h := key (blockOp A Ys) (fun U hU' => ((hG _).2 ⟨Ys, rfl⟩ U hU'))
    rw [trace_blockOp_mul, trace_blockOp_mul] at h
    rw [Finset.sum_eq_single l, Finset.sum_eq_single l] at h
    · simpa [hYs, ptrA_blockOp, Matrix.mul_smul, Matrix.trace_smul] using h
    · intro l' _ hl'
      simp [hYs, Function.update_of_ne hl']
    · simp
    · intro l' _ hl'
      simp [hYs, Function.update_of_ne hl']
    · simp
  have hc : (Fintype.card (A l) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (A l) := Fintype.card_pos_iff.2 inferInstance
    exact_mod_cast this.ne'
  ext b b'
  have := hX (Matrix.single b' b 1)
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ptrA] at this ⊢
  have e : ∀ f : B l → B l → ℂ,
      (∑ i, ∑ j, if b' = i ∧ b = j then f j i else 0) = f b b' := by
    intro f
    simp [ite_and, Finset.sum_ite_eq]
  rw [e (fun j i => X l j i), e (fun j i => ∑ α, ρ ⟨l, (α, j)⟩ ⟨l, (α, i)⟩)] at this
  rw [← this]
  field_simp

end Twirl

end FormalResearch.QIB
