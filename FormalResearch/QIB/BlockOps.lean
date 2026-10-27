import Mathlib
import FormalResearch.FrameFree.HelstromPure
import FormalResearch.FrameFree.HelstromTwirlBound

/-!
# Isotypic block operators `⊕_λ I_{V_λ} ⊗ X_λ` (coordinates for `lem:blockdecomp`)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (pure finite-dimensional linear algebra; no
hypothesis on any group appears in this file).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, Section "Finite-copy blocks",
Lemma `lem:blockdecomp`.  The space carrying the sector decomposition `⊕_λ V_λ ⊗ M_λ` is realised in
coordinates by the index type `Idx A B = Σ λ, A λ × B λ` (carrier index `A λ`, multiplicity index
`B λ`).  Nothing here constructs the Schur-Weyl decomposition of a physical representation; the
coordinates are the input (compare `QIA/IsotypicMultiplicityReduction.lean`, which does the same).

* `blockOp A X = ⊕_λ I_{A λ} ⊗ X_λ` (`Matrix.blockDiagonal'` of Kronecker products), with its
  entries (`blockOp_apply_same`, `blockOp_apply_ne`), algebra (`blockOp_sub`, `blockOp_one`, ...) and
  `blockOp_inj`;
* `slice v λ α`, the multiplicity vector of a vector at carrier index `α`;
* `tau v λ = Σ_α |slice v λ α⟩⟨slice v λ α| = Tr_{V_λ}(Π_λ |v⟩⟨v| Π_λ)` (the multiplicity block);
* `qf_blockOp`, `qf_blockOp_self`: `⟨v| ⊕ I⊗X_λ |w⟩ = Σ_λ Σ_α ⟨v_{λα}|X_λ|w_{λα}⟩` and
  `⟨v| ⊕ I⊗X_λ |v⟩ = Σ_λ Tr(X_λ τ_λ(v))`;
* `blockOp_isEffect_iff`: `0 ≤ ⊕ I⊗X_λ ≤ 1` iff every `0 ≤ X_λ ≤ 1` (carriers nonempty).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect qf tr_mul_vecMulVec)

section Blocks

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- Coordinates of `⊕_λ V_λ ⊗ M_λ`: sector, carrier index, multiplicity index. -/
abbrev Idx (A B : Λ → Type*) := Σ l, A l × B l

/-- `⊕_λ I_{A λ} ⊗ X_λ`. -/
noncomputable def blockOp (A : Λ → Type*) [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)]
    (X : ∀ l, Matrix (B l) (B l) ℂ) : Matrix (Idx A B) (Idx A B) ℂ :=
  Matrix.blockDiagonal' fun l => (1 : Matrix (A l) (A l) ℂ) ⊗ₖ X l

theorem blockOp_apply_same (X : ∀ l, Matrix (B l) (B l) ℂ) (l : Λ) (α α' : A l) (b b' : B l) :
    blockOp A X ⟨l, (α, b)⟩ ⟨l, (α', b')⟩ = if α = α' then X l b b' else 0 := by
  unfold blockOp
  rw [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem blockOp_apply_ne (X : ∀ l, Matrix (B l) (B l) ℂ) {l l' : Λ} (h : l ≠ l')
    (p : A l × B l) (q : A l' × B l') : blockOp A X ⟨l, p⟩ ⟨l', q⟩ = 0 :=
  Matrix.blockDiagonal'_apply_ne _ _ _ h

theorem blockOp_sub (X Y : ∀ l, Matrix (B l) (B l) ℂ) :
    blockOp A (fun l => X l - Y l) = blockOp A X - blockOp A Y := by
  unfold blockOp
  rw [← Matrix.blockDiagonal'_sub]
  congr 1; funext l
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [Matrix.kronecker_apply, mul_sub]

theorem blockOp_one : blockOp A (fun l => (1 : Matrix (B l) (B l) ℂ)) = 1 := by
  unfold blockOp
  rw [show (fun l => (1 : Matrix (A l) (A l) ℂ) ⊗ₖ (1 : Matrix (B l) (B l) ℂ)) = fun _ => 1 from
    funext fun l => Matrix.one_kronecker_one]
  exact Matrix.blockDiagonal'_one

theorem blockOp_conjTranspose (X : ∀ l, Matrix (B l) (B l) ℂ) :
    (blockOp A X)ᴴ = blockOp A (fun l => (X l)ᴴ) := by
  unfold blockOp
  rw [Matrix.blockDiagonal'_conjTranspose]
  congr 1; funext l
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Every sector has a carrier vector, so `X ↦ blockOp X` is injective. -/
theorem blockOp_inj [∀ l, Nonempty (A l)] {X Y : ∀ l, Matrix (B l) (B l) ℂ}
    (h : blockOp A X = blockOp A Y) : X = Y := by
  funext l
  ext b b'
  obtain ⟨α⟩ := ‹∀ l, Nonempty (A l)› l
  have := congrFun (congrFun h ⟨l, (α, b)⟩) ⟨l, (α, b')⟩
  simpa [blockOp_apply_same] using this

/-! ### Vectors: slices and the multiplicity block -/

/-- The multiplicity vector of `v` at carrier index `α` of sector `l`. -/
def slice (v : Idx A B → ℂ) (l : Λ) (α : A l) : B l → ℂ := fun b => v ⟨l, (α, b)⟩

/-- `τ_λ(v) = Σ_α |v_{λα}⟩⟨v_{λα}|`, i.e. `Tr_{V_λ} (Π_λ |v⟩⟨v| Π_λ)` in the multiplicity space. -/
noncomputable def tau (v : Idx A B → ℂ) (l : Λ) : Matrix (B l) (B l) ℂ :=
  ∑ α, Matrix.vecMulVec (slice v l α) (star (slice v l α))

theorem tau_apply (v : Idx A B → ℂ) (l : Λ) (b b' : B l) :
    tau v l b b' = ∑ α, v ⟨l, (α, b)⟩ * star (v ⟨l, (α, b')⟩) := by
  simp [tau, slice, Matrix.sum_apply, Matrix.vecMulVec_apply]

theorem tau_posSemidef (v : Idx A B → ℂ) (l : Λ) : (tau v l).PosSemidef := by
  unfold tau
  exact Matrix.posSemidef_sum _ fun α _ => Matrix.posSemidef_vecMulVec_self_star _

theorem tau_isHermitian (v : Idx A B → ℂ) (l : Λ) : (tau v l).IsHermitian :=
  (tau_posSemidef v l).isHermitian

theorem blockOp_mulVec_apply (X : ∀ l, Matrix (B l) (B l) ℂ) (w : Idx A B → ℂ) (l : Λ) (α : A l)
    (b : B l) :
    (blockOp A X *ᵥ w) ⟨l, (α, b)⟩ = (X l *ᵥ slice w l α) b := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single l]
  · simp only [blockOp_apply_same, ite_mul, zero_mul, slice]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · intro l' _ hl'
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b' _ => ?_
    rw [blockOp_apply_ne _ (Ne.symm hl'), zero_mul]
  · simp

theorem qf_blockOp (X : ∀ l, Matrix (B l) (B l) ℂ) (v w : Idx A B → ℂ) :
    qf (blockOp A X) v w = ∑ l, ∑ α, star (slice v l α) ⬝ᵥ (X l *ᵥ slice w l α) := by
  unfold qf
  simp only [dotProduct, Fintype.sum_sigma, Fintype.sum_prod_type, Pi.star_apply,
    blockOp_mulVec_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ => rfl

theorem qf_blockOp_self (X : ∀ l, Matrix (B l) (B l) ℂ) (v : Idx A B → ℂ) :
    qf (blockOp A X) v v = ∑ l, (X l * tau v l).trace := by
  rw [qf_blockOp]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold tau
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [tr_mul_vecMulVec]

/-! ### Positivity -/

theorem blockOp_posSemidef_iff [∀ l, Nonempty (A l)] (X : ∀ l, Matrix (B l) (B l) ℂ) :
    (blockOp A X).PosSemidef ↔ ∀ l, (X l).PosSemidef := by
  constructor
  · intro h l
    obtain ⟨α⟩ := ‹∀ l, Nonempty (A l)› l
    have := h.submatrix (fun b : B l => (⟨l, (α, b)⟩ : Idx A B))
    convert this using 1
    ext b b'
    simp [blockOp_apply_same]
  · intro h
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [Matrix.IsHermitian, blockOp_conjTranspose]
      congr 1; funext l
      exact (h l).isHermitian
    · have := qf_blockOp X v v
      unfold qf at this
      rw [this]
      refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun α _ => ?_
      exact (Matrix.posSemidef_iff_dotProduct_mulVec.1 (h l)).2 _

theorem blockOp_isEffect_iff [∀ l, Nonempty (A l)] (X : ∀ l, Matrix (B l) (B l) ℂ) :
    IsEffect (blockOp A X) ↔ ∀ l, IsEffect (X l) := by
  have e : (1 : Matrix (Idx A B) (Idx A B) ℂ) - blockOp A X =
      blockOp A (fun l => (1 : Matrix (B l) (B l) ℂ) - X l) := by
    rw [blockOp_sub, blockOp_one]
  unfold IsEffect
  rw [e, blockOp_posSemidef_iff, blockOp_posSemidef_iff]
  exact ⟨fun h l => ⟨h.1 l, h.2 l⟩, fun h => ⟨fun l => (h l).1, fun l => (h l).2⟩⟩

end Blocks

end FormalResearch.QIB
