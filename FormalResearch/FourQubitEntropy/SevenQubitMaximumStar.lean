import FormalResearch.FourQubitEntropy.SevenQubitMaximumReduction
import FormalResearch.FourQubitEntropy.SevenQubitIcoStarValue

/-!
# The final reduction of `thm:seven-entropy-global-maximum` with `E_* = E₃(ψ_{x_*})`

`SevenQubitMaximumReduction.seven_entropy_max_reduction` takes the SC-2 witness
`(59307/20000) ln 2 < E_*` as a hypothesis. For `E_* = E₃(x_*)`, the family maximum, that witness is
proved (`StarValue.sc2_witness`), so it disappears from the statement.

Remaining hypotheses (Prop arguments): `SevenPurityBound`, the joint majorant bound `JointMajorantBound P5`
(from AH-6, the scalar majorant of `lem:seven-joint-scalar-majorant`) and the localized bound `LocalizedBound P5 (E₃ x_*)` (E7-1). **This is not a proof of the
maximum**: it is the reduction to those three hypotheses. That `E_*` is the entropy of the seven-qubit
state `ψ_{x_*}` itself (attainment) is also not formalized here; `E3` is the family entropy function.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco
open MaximumReduction

theorem seven_entropy_max_reduction_star (hPB : SevenPurityBound)
    {P5 : (BitString → ℂ) → ℝ} (hJ : JointMajorantBound P5) :
    ∃ c : ℝ, (∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
      (LocalizedBound P5 (E3 c) → ∀ ψ : BitString → ℂ, UnitVec ψ → meanEntropy3 ψ ≤ E3 c) := by
  obtain ⟨c, hmax, hwit⟩ := StarValue.sc2_witness
  exact ⟨c, hmax, fun hL ψ hψ => seven_entropy_max_reduction hPB hwit hJ hL ψ hψ⟩

end FormalResearch.FourQubitEntropy.SevenQubitConseq
