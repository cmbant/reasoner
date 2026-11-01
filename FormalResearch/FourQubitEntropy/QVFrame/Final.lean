import FormalResearch.FourQubitEntropy.QVFrame.Assembly

/-!
# From `P K P = 0` to a vanishing Hermitian form

* `bilin_eq_zero_of_symmetrised`: `P K P = 0` (`P` the `S_n` copy-symmetriser of `QVBlock`) gives the bilinear
  vanishing `⟨u^{⊗n}, K v^{⊗n}⟩ = 0` for *independent* `u, v` (the Hermitian form needs `u = z̄`, `v = z`).
-/

open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

theorem bilin_eq_zero_of_symmetrised {n : ℕ} (K : Matrix (Cfg n) (Cfg n) ℂ)
    (hK : copySym ℂ (Fin 4) (Fin 2) n * K * copySym ℂ (Fin 4) (Fin 2) n = 0) (u v : Site → ℂ) :
    copyPower u n ⬝ᵥ (K *ᵥ copyPower v n) = 0 := by
  have hr : copySym ℂ (Fin 4) (Fin 2) n *ᵥ copyPower v n = copyPower v n :=
    copySym_mulVec_copyPower v
  have hl : copyPower u n ᵥ* copySym ℂ (Fin 4) (Fin 2) n = copyPower u n :=
    copyPower_vecMul_copySym u
  have h : copyPower u n ⬝ᵥ ((copySym ℂ (Fin 4) (Fin 2) n * K * copySym ℂ (Fin 4) (Fin 2) n) *ᵥ copyPower v n) =
      copyPower u n ⬝ᵥ (K *ᵥ copyPower v n) := by
    have : copyPower u n ⬝ᵥ ((copySym ℂ (Fin 4) (Fin 2) n * K * copySym ℂ (Fin 4) (Fin 2) n) *ᵥ copyPower v n) =
        copyPower u n ⬝ᵥ (copySym ℂ (Fin 4) (Fin 2) n *ᵥ (K *ᵥ (copySym ℂ (Fin 4) (Fin 2) n *ᵥ copyPower v n))) := by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [this, hr, Matrix.dotProduct_mulVec (copyPower u n) (copySym ℂ (Fin 4) (Fin 2) n), hl]
  rw [← h, hK]
  simp

end FormalResearch.FourQubitEntropy.QVFrame
