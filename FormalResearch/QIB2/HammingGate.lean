import Mathlib

namespace FormalResearch.QIB2

open Complex

/-- Coefficients of the canonical triplet/singlet phase gate
`U = a I + b τ`. -/
noncomputable def gateA : ℂ := (1 + I) / 2
noncomputable def gateB : ℂ := (1 - I) / 2

theorem gate_coeff_sum : gateA + gateB = 1 := by
  simp [gateA, gateB]
  ring

theorem gate_coeff_sq_sum : gateA^2 + gateB^2 = 0 := by
  unfold gateA gateB
  ring_nf
  norm_num [Complex.I_sq]

theorem gate_coeff_cross : 2 * gateA * gateB = 1 := by
  unfold gateA gateB
  ring_nf
  norm_num [Complex.I_sq]

/-- Algebraic core of the exact Hamming gate identity: for any commuting
involution `τ`, the canonical phase gate squares to `τ`.  The full `d`-rung
statement `U_d² = ∏ τ_i` follows by tensoring this one-rung identity. -/
theorem canonical_gate_sq (τ : ℂ) (hτ : τ^2 = 1) :
    (gateA + gateB * τ)^2 = τ := by
  calc
    (gateA + gateB * τ)^2 =
        gateA^2 + (2 * gateA * gateB) * τ + gateB^2 * τ^2 := by ring
    _ = gateA^2 + τ + gateB^2 := by rw [gate_coeff_cross, hτ]; ring
    _ = τ + (gateA^2 + gateB^2) := by ring
    _ = τ := by rw [gate_coeff_sq_sum, add_zero]

/-- On an even swap eigenvalue the gate phase is `1`. -/
theorem canonical_gate_at_plus : gateA + gateB = 1 := gate_coeff_sum

/-- On an odd swap eigenvalue the gate phase is `i`. -/
theorem canonical_gate_at_minus : gateA - gateB = I := by
  simp [gateA, gateB]
  ring

end FormalResearch.QIB2
