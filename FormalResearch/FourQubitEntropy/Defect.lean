import FormalResearch.FourQubitEntropy.Transfer
import FormalResearch.FourQubitEntropy.Identity

/-!
# The sextic identity for every complex vector

`sexticDefect z w = 0` for all `z w : State ℂ`: the polynomial identity of `Identity.lean`,
evaluated at arbitrary complex values of the 32 variables.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- The values of the 32 variables `z_{abcd}`, `w_{abcd}`. -/
def varValues (z w : State ℂ) : Fin 32 → ℂ := fun i =>
  let j := i.val % 16
  let a : Fin 2 := Fin.ofNat 2 (j / 8)
  let b : Fin 2 := Fin.ofNat 2 (j / 4)
  let c : Fin 2 := Fin.ofNat 2 (j / 2)
  let d : Fin 2 := Fin.ofNat 2 j
  if i.val < 16 then z a b c d else w a b c d

theorem map_zSP (z w : State ℂ) : zSP.map (evSP (varValues z w)) = z := by
  funext a b c d
  simp only [State.map, zSP, evSP_varSP]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

theorem map_wSP (z w : State ℂ) : wSP.map (evSP (varValues z w)) = w := by
  funext a b c d
  simp only [State.map, wSP, evSP_varSP]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

/-- The sharp sextic identity `96 F - 72 n W₁ - Σᵢ 36‖Vᵢ - 8Uᵢ‖² - 144 Σ_{i<j} ‖(Rᵢ^{(i)} - Rⱼ^{(j)}) z‖² = 0`,
for all complex `z`, `w`. -/
theorem sexticDefect_zero (z w : State ℂ) : sexticDefect z w = 0 := by
  have h := (opsHom_evSP (varValues z w)).sexticDefect zSP wSP
  rw [map_zSP, map_wSP, sexticDefect_check] at h
  exact h.symm

end FormalResearch.FourQubitEntropy
