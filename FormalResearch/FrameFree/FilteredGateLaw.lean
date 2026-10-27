import FormalResearch.FrameFree.FilteredGateReduce
import FormalResearch.FrameFree.FilteredGateEcho
import FormalResearch.FrameFree.FilteredGateReal

/-!
# Filtered-gate law with a unitary spectator (`cor:ftg`)

Paper P `cor:ftg` (recalled from QI-B `thm:ftg`).  For `U = U_c` the Cartan gate, arbitrary
`A, B, C` and a unitary `W`,
`|Tr[U (A ⊗ B) U (W ⊗ C)]|² ≤ 2 (1 + δ) ‖(A ⊗ B) U (W ⊗ C)‖_F²`, `δ = max_j |cos 4c_j|`,
i.e. `R_W(A,B,C) ≤ 1 + δ`.  The bound is attained by a Pauli echo at `W = 1` (`echo_attain`).
-/

open scoped Matrix Kronecker ComplexConjugate

namespace FormalResearch.FrameFree.FTG

/-- **Filtered-gate law with a unitary spectator.** -/
theorem filtered_gate_law (c : Fin 3 → ℝ) (A B C W : M2) (hW : Wᴴ * W = 1) :
    ‖(Ug c * kr A B * Ug c * kr W C).trace‖ ^ 2 ≤
      2 * (1 + dl c) * fro2 (kr A B * Ug c * kr W C) :=
  Law_all c A B C W hW

/-- The law in terms of `ov` and `gm`. -/
theorem ov_sq_le (c : Fin 3 → ℝ) (A B C W : M2) (hW : Wᴴ * W = 1) :
    ‖ov c A B W C‖ ^ 2 ≤ (1 + dl c) * (2 * fro2 (gm c A B W C)) := by
  have h := filtered_gate_law c A B C W hW
  have e : ov c A B W C = (Ug c * kr A B * Ug c * kr W C).trace := by
    unfold ov gm; simp only [Matrix.mul_assoc]
  rw [e]
  unfold gm
  linarith

/-- Sharpness: the constant `1 + δ` is attained at `W = 1`, and never exceeded for unitary `W`. -/
theorem filtered_gate_sharp (c : Fin 3 → ℝ) :
    (∀ A B C W : M2, Wᴴ * W = 1 →
      ‖ov c A B W C‖ ^ 2 ≤ (1 + dl c) * (2 * fro2 (gm c A B W C))) ∧
    ∃ A B C : M2, fro2 (gm c A B 1 C) = 4 ∧
      ‖ov c A B 1 C‖ ^ 2 = (1 + dl c) * (2 * fro2 (gm c A B 1 C)) :=
  ⟨fun A B C W hW => ov_sq_le c A B C W hW, echo_attain c⟩

end FormalResearch.FrameFree.FTG
