import Mathlib

namespace FormalResearch.QIB2

open Complex

/-!
# QI-B2 canonical Hamming/Krawtchouk phase algebra

Source: `QI-B/B2-hamming/results/three_band_hamming_heat_kernel.tex`, section
"Exact Hamming/Krawtchouk phase algebra" (`eq:hammingU`): `U = (1+i)/2 I +
(1-i)/2 tau`, `U^(tensor d) = sum_m i^m E_m = sum_r ((1+i)/2)^(d-r)
((1-i)/2)^r W_r`, `W_r E_m = K_r(m) E_m`, `K_r(m) = sum_l (-1)^l C(m,l)
C(d-m,r-l)`.  The `QIB2` modules prove the scalar/combinatorial content on the
Boolean-cube model of the swap eigenbasis: the Krawtchouk formula and
generating function, the Bose--Mesner eigenaction of the radius-`r` orbit sum
on a Walsh character, the phase `i^|T|` for every Walsh label, and the
`choose d m` multiplicity of weight `m`.  They do not construct the two-qubit
swap operators `tau_i`, the projectors `E_m` or the operator identity on
`(C^4)^(tensor d)`, and `U_d^2 = prod tau_i` is formalized only for one rung
(`canonical_gate_sq`).
-/

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
