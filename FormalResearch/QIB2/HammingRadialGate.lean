import Mathlib
import FormalResearch.QIB2.HammingGate
import FormalResearch.QIB2.KrawtchoukGenerating

namespace FormalResearch.QIB2

open Complex
open scoped BigOperators

/-- Elementary homogenization identity used to convert the ordinary
Krawtchouk generating polynomial into the radial gate expansion. -/
theorem homogenize_binary_generating {d m : Nat} (hm : m ≤ d)
    (a b : ℂ) (ha : a ≠ 0) :
    a^d * (1 - b / a)^m * (1 + b / a)^(d - m) =
      (a - b)^m * (a + b)^(d - m) := by
  have hsub : 1 - b / a = (a - b) / a := by
    field_simp [ha]
  have hadd : 1 + b / a = (a + b) / a := by
    field_simp [ha]
  rw [hsub, hadd, div_pow, div_pow]
  have hpow : a^m * a^(d - m) = a^d := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  field_simp [ha, hpow]
  ring

/-- The canonical gate coefficient `a=(1+i)/2` is nonzero. -/
theorem gateA_ne_zero : gateA ≠ 0 := by
  intro ha
  have h := gate_coeff_cross
  rw [ha] at h
  norm_num at h

/-- Exact radial spectral law.  The Krawtchouk eigenvalues, assembled with the
canonical local-gate ratio `b/a`, reproduce precisely the phase `i^m` on the
Walsh sector of weight `m`. -/
theorem canonical_gate_krawtchouk_phase {d m : Nat} (hm : m ≤ d) :
    gateA^d *
      (∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
        (binaryKrawtchouk d m r : ℂ) * (gateB / gateA)^r) =
      I^m := by
  rw [binaryKrawtchouk_generating_eval_complex]
  rw [homogenize_binary_generating hm gateA gateB gateA_ne_zero]
  rw [canonical_gate_at_minus, gate_coeff_sum]
  simp

end FormalResearch.QIB2
