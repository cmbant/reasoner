import FormalResearch.FourQubitEntropy.Tradeoff
import FormalResearch.FourQubitEntropy.Classify
import FormalResearch.FourQubitEntropy.EqualityConverse

/-!
# The moments `n, P, T` and the sextic `F` are local-unitary invariant

Used to transfer the critical-slice identity from `G(v)` to a general critical vector
(`prop:fqe-moment-zeros`). Proved, no hypotheses, no `native_decide`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

theorem trace_conj_two {K R : Mat4} (hK : Kᴴ * K = 1) :
    Matrix.trace ((K * R * Kᴴ) * (K * R * Kᴴ)) = Matrix.trace (R * R) := by
  have e : (K * R * Kᴴ) * (K * R * Kᴴ) = K * (R * R) * Kᴴ := by
    calc _ = K * R * (Kᴴ * K) * R * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, hK, Matrix.mul_one]

theorem trace_conj_three {K R : Mat4} (hK : Kᴴ * K = 1) :
    Matrix.trace ((K * R * Kᴴ) * (K * R * Kᴴ) * (K * R * Kᴴ)) = Matrix.trace (R * R * R) := by
  have e : (K * R * Kᴴ) * (K * R * Kᴴ) * (K * R * Kᴴ) = K * (R * R * R) * Kᴴ := by
    calc _ = K * R * (Kᴴ * K) * R * (Kᴴ * K) * R * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, hK, Matrix.mul_one]

theorem red13_localApply {a b c d : Op1} (hb : bᴴ * b = 1) (hd : dᴴ * d = 1) (ψ : Psi) :
    red13 (localApply a b c d ψ) = kron a c * red13 ψ * (kron a c)ᴴ := by
  rw [red13_eq_swap, red13_eq_swap, swap23_localApply a c b d ψ, red12_localApply hb hd]

theorem red14_localApply {a b c d : Op1} (hc : cᴴ * c = 1) (hb : bᴴ * b = 1) (ψ : Psi) :
    red14 (localApply a b c d ψ) = kron a d * red14 ψ * (kron a d)ᴴ := by
  rw [red14_eq_swap, red14_eq_swap, swap24_localApply a d c b ψ, red12_localApply hc hb]

theorem purity_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (hd : dᴴ * d = 1) (ψ : Psi) : purity (localApply a b c d ψ) = purity ψ := by
  unfold purity
  rw [red12_localApply hc hd, red13_localApply hb hd, red14_localApply hc hb,
    trace_conj_two (kron_unitary ha hb), trace_conj_two (kron_unitary ha hc),
    trace_conj_two (kron_unitary ha hd)]

theorem cubicMoment_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1)
    (hc : cᴴ * c = 1) (hd : dᴴ * d = 1) (ψ : Psi) :
    cubicMoment (localApply a b c d ψ) = cubicMoment ψ := by
  unfold cubicMoment
  rw [red12_localApply hc hd, red13_localApply hb hd, red14_localApply hc hb,
    trace_conj_three (kron_unitary ha hb), trace_conj_three (kron_unitary ha hc),
    trace_conj_three (kron_unitary ha hd)]

/-- **`F` is invariant under local unitaries** (proved). -/
theorem sexticF_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (hd : dᴴ * d = 1) (ψ : Psi) : sexticF (localApply a b c d ψ) = sexticF ψ := by
  unfold sexticF
  rw [normSqPsi_localApply ha hb hc hd, purity_localApply ha hb hc hd,
    cubicMoment_localApply ha hb hc hd]

theorem sexticF_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) : sexticF ψ = sexticF φ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact sexticF_localApply ha hb hc hd φ

theorem normSqPsi_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) : normSqPsi ψ = normSqPsi φ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact normSqPsi_localApply ha hb hc hd φ

end FormalResearch.FourQubitEntropy.PaperECritical
