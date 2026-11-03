module

public import FormalResearch.GurvitsBarnum.Basic
public import MathLab.ChainTheory.PPTCriterion

/-!
# The 2⊗3 PPT criterion, from the vendored math-lab proof

The Horodecki–Horodecki–Horodecki (1996) / Woronowicz (1976) theorem that every PPT operator on
`ℂ² ⊗ ℂ³` is separable is not in Mathlib.  It is proved in the vendored third-party development
`ThirdParty/math-lab` (see `ThirdParty/math-lab/NOTICE.md`) as `ChainPPT.pptSeparable23`.  This file
defines the partial transpose `ptFirst` on the first factor and the statement `PPTSeparable23` in the
conventions of this repository (Mathlib `PosSemidef`, `GurvitsBarnum.IsSeparable`), and proves
`pptSeparable23 : PPTSeparable23` by transporting math-lab's theorem.  It is the input of the
product-kernel lemma `ppt_product_kernel` (`ProductKernel.lean`).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.GurvitsBarnum
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The partial transpose on the first tensor factor: `(ρ^{T_1})_{(i,k),(j,l)} = ρ_{(j,k),(i,l)}`. -/
def ptFirst (ρ : Matrix (ι × κ) (ι × κ) ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.of fun p q => ρ (q.1, p.2) (p.1, q.2)

theorem ptFirst_apply (ρ : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) (k l : κ) :
    ptFirst ρ (i, k) (j, l) = ρ (j, k) (i, l) := rfl

/-- The 2⊗3 PPT criterion (Horodecki–Horodecki–Horodecki 1996): every positive operator on
`ℂ² ⊗ ℂ³` with positive semidefinite partial transpose is separable.  Proved as `pptSeparable23`. -/
def PPTSeparable23 : Prop :=
  ∀ ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ, ρ.PosSemidef → (ptFirst ρ).PosSemidef →
    IsSeparable ρ

/-- Mathlib's `PosSemidef` gives math-lab's quadratic-form predicate `IsPSD`. -/
theorem isPSD_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (h : P.PosSemidef) : ChainDuality.IsPSD P := fun v => by
  have h0 : (0 : ℂ) ≤ star v ⬝ᵥ (P *ᵥ v) := (Matrix.posSemidef_iff_dotProduct_mulVec.1 h).2 v
  exact ⟨(Complex.nonneg_iff.1 h0).1, (Complex.nonneg_iff.1 h0).2.symm⟩

/-- Our `ptFirst` is the full transpose of math-lab's partial transpose on the second factor. -/
theorem ptFirst_eq_transpose_pt (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    ptFirst ρ = (ChainDuality.pt ρ)ᵀ := by
  ext ⟨i, k⟩ ⟨j, l⟩; rfl

/-- `prodRankOne a b` is math-lab's rank-one projector on the product vector `a ⊗ b`. -/
theorem prodRankOne_eq_vecMulVec_prodVec (a : Fin 2 → ℂ) (b : Fin 3 → ℂ) :
    GurvitsBarnum.prodRankOne a b =
      vecMulVec (ChainDuality.prodVec a b) (star (ChainDuality.prodVec a b)) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [prodRankOne, kroneckerMap_apply, ChainDuality.prodVec, vecMulVec_apply, Pi.star_apply,
    star_mul']
  ring

/-- **Horodecki–Horodecki–Horodecki 2⊗3 criterion**: every PPT operator on `ℂ² ⊗ ℂ³` is separable.
Proved via the vendored `ChainPPT.pptSeparable23`. -/
theorem pptSeparable23 : PPTSeparable23 := by
  intro ρ hρ hT
  have hpt : ChainDuality.IsPSD (ChainDuality.pt ρ) := by
    apply ChainWoronowicz.isPSD_of_transpose
    rw [← ptFirst_eq_transpose_pt]
    exact isPSD_of_posSemidef hT
  obtain ⟨r, x, y, hxy⟩ := ChainPPT.pptSeparable23 ρ ⟨isPSD_of_posSemidef hρ, hpt⟩
  exact ⟨r, x, y, by rw [hxy]; exact Finset.sum_congr rfl fun s _ =>
    (prodRankOne_eq_vecMulVec_prodVec _ _).symm⟩

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.pptSeparable23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.pptSeparable23
