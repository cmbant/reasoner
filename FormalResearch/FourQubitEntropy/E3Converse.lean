import FormalResearch.FourQubitEntropy.Corollaries
import FormalResearch.FourQubitEntropy.PaperECriticalZeroOrbits
import FormalResearch.FourQubitEntropy.Renyi

/-!
# `cor:fqe-e3`: the equality case, both directions

`Corollaries.lean` proves `Σ_j e₃(ρ_{1j}) = (6 - P - F)/36 ≤ 5/36` and that the vectors of the two `M₄`
orbits attain `5/36`. Here the converse: for a unit vector, `Σ_j e₃(ρ_{1j}) = 5/36` forces `P = 1` and
`F = 0`, and by the classification of the zeros of `F` (`moment_zeros`, three of whose five orbits have
`P = 3/2`) the vector lies in an orbit of `M₄` or `conj M₄`.
-/

namespace FormalResearch.FourQubitEntropy

open PaperECritical

/-- **Equality case of `cor:fqe-e3`**: for a unit vector, `Σ_j e₃(ρ_{1j}) = 5/36` iff `ψ` is a
local-unitary image of `M₄` or of `conj M₄`. -/
theorem e3_sum_eq_iff (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    cutE3 (red12_herm ψ) + cutE3 (red13_herm ψ) + cutE3 (red14_herm ψ) = 5 / 36 ↔
      LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  constructor
  · intro h
    have h1 := e3_sum_eq ψ hψ
    have hP := purity_ge ψ
    have hF := sexticF_nonneg ψ
    rw [hψ] at hP
    have hP1 : purity ψ = 1 := by linarith
    have hF0 : sexticF ψ = 0 := by linarith
    rcases (moment_zeros ψ hψ).mp hF0 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
      rw [purity_localApply ha hb hc hd, bell2_vals.2.1] at hP1
      norm_num at hP1
    · exfalso
      obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
      rw [purity_localApply ha hb hc hd, bell13_vals.2.1] at hP1
      norm_num at hP1
    · exfalso
      obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
      rw [purity_localApply ha hb hc hd, bell14_vals.2.1] at hP1
      norm_num at hP1
  · rintro (h | h)
    · exact e3_sum_of_cutQuadratics hψ (CutQuadratics_of_LU M4_unit M4_cutQuadratics h).2
    · exact e3_sum_of_cutQuadratics hψ
        (CutQuadratics_of_LU (by rw [normSqPsi_conj]; exact M4_unit) M4_cutQuadratics.conj h).2

/-- info: 'FormalResearch.FourQubitEntropy.e3_sum_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms e3_sum_eq_iff

end FormalResearch.FourQubitEntropy
