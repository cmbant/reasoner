module

public import FormalResearch.PPTThreeQubit.CurveParam
public import FormalResearch.PPTThreeQubit.ProductKernelThree

/-!
# The universal moment cone for fully-PPT GME states

Combines `lem:ppt3-product-kernel` (`ProductKernelThree`) with `thm:ppt3-universal-moments`
(`CurveParam`): for a fully-PPT three-qubit state `ρ` that is not biseparable, any basis matrix `K` of a
subspace of its kernel has no nonzero cut-product vector in its range, so the universal moment-cone
description holds for every `B` with `Kᴴ B = 0`.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped ComplexOrder

noncomputable section

/-- `thm:ppt3-universal-moments` for the support of a fully-PPT GME state.  `B`
is a basis matrix of a five-dimensional `R` and `K` a basis matrix of an `8 × 3` block of the kernel of `ρ` with `Kᴴ B = 0` (for a rank-five `ρ`, `R = range ρ` and
`range K = ker ρ`). -/
theorem ppt3_universal_moments_of_gme (ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hρ : ρ.PosSemidef) (hA : (ptA ρ).PosSemidef) (hB' : (ptB ρ).PosSemidef)
    (hC : (ptC ρ).PosSemidef) (hg : IsGME ρ)
    (B : Matrix (Fin 8) (Fin 5) ℂ) (K : Matrix (Fin 8) (Fin 3) ℂ)
    (hB : Function.Injective B.mulVec) (hK : Function.Injective K.mulVec) (hKB : Kᴴ * B = 0)
    (hKρ : ρ * K = 0) :
    ∃ T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ, (∀ c, IsUnit (T c).det) ∧ CutCurve B T ∧
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) ↔ InMomentCone T X) ∧
      (∀ H : Matrix (Fin 5) (Fin 5) ℂ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) → 0 ≤ (trace (H * X)).re) ↔
          ∀ (c : Fin 3) (a : Fin 2 → ℂ),
            0 ≤ (star (nuVec a) ⬝ᵥ ((T c)ᴴ * H * T c) *ᵥ nuVec a).re) := by
  refine ppt3_universal_moments B K hB hKB fun y hy => ?_
  refine kernel_free_of_gme ρ hρ hA hB' hC hg (K *ᵥ y) ?_ ?_
  · intro h0
    exact hy (hK (by rw [h0, mulVec_zero]))
  · rw [mulVec_mulVec, hKρ, zero_mulVec]

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_universal_moments_of_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.ppt3_universal_moments_of_gme
