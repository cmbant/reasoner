import FormalResearch.PPTThreeQubit.Basic

/-!
# The three cuts as `ℂ² ⊗ ℂ⁴`

Each single-qubit cut `A|BC`, `B|AC`, `C|AB` of a three-qubit vector `Fin 8 → ℂ` is a reindexing
`Fin 8 ≃ Fin 2 × Fin 4` (qubit of the cut, remaining two qubits) matching `IsProdA`, `IsProdB`,
`IsProdC` of `FormalResearch.PPTThreeQubit.Basic`.
-/

namespace FormalResearch.PPTThreeQubit

noncomputable section

/-- The reindexing `Fin 8 ≃ Fin 2 × Fin 4` of the cut `A|BC`. -/
def eqA : Fin 8 ≃ Fin 2 × Fin 4 where
  toFun i := (⟨i.val / 4, by omega⟩, ⟨i.val % 4, by omega⟩)
  invFun p := ⟨4 * p.1.val + p.2.val, by omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by obtain ⟨i, k⟩ := p; fin_cases i <;> fin_cases k <;> rfl

/-- The reindexing `Fin 8 ≃ Fin 2 × Fin 4` of the cut `B|AC`. -/
def eqB : Fin 8 ≃ Fin 2 × Fin 4 where
  toFun i := (⟨i.val / 2 % 2, by omega⟩, ⟨2 * (i.val / 4) + i.val % 2, by omega⟩)
  invFun p := ⟨4 * (p.2.val / 2) + 2 * p.1.val + p.2.val % 2, by omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by obtain ⟨i, k⟩ := p; fin_cases i <;> fin_cases k <;> rfl

/-- The reindexing `Fin 8 ≃ Fin 2 × Fin 4` of the cut `C|AB`. -/
def eqC : Fin 8 ≃ Fin 2 × Fin 4 where
  toFun i := (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩)
  invFun p := ⟨2 * p.2.val + p.1.val, by omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by obtain ⟨i, k⟩ := p; fin_cases i <;> fin_cases k <;> rfl

/-- A vector is a product `α ⊗ μ` across the cut described by `e : Fin 8 ≃ Fin 2 × Fin 4`. -/
def IsProdE (e : Fin 8 ≃ Fin 2 × Fin 4) (x : Fin 8 → ℂ) : Prop :=
  ∃ (α : Fin 2 → ℂ) (μ : Fin 4 → ℂ), ∀ i, x i = α (e i).1 * μ (e i).2

theorem isProdA_iff (x : Fin 8 → ℂ) : IsProdA x ↔ IsProdE eqA x := Iff.rfl

theorem isProdB_iff (x : Fin 8 → ℂ) : IsProdB x ↔ IsProdE eqB x := Iff.rfl

theorem isProdC_iff (x : Fin 8 → ℂ) : IsProdC x ↔ IsProdE eqC x := Iff.rfl

end

end FormalResearch.PPTThreeQubit
