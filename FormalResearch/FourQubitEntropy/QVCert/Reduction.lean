import FormalResearch.FourQubitEntropy.RenyiFullHeadlineQV
import FormalResearch.FourQubitEntropy.QVCert.QVDefect
import FormalResearch.FourQubitEntropy.QVCert.Covariants

/-!
# Reduction of (QV) to the certificate identity

Paper E, `sup_renyi.tex`, `sec:sup-qk`: `thm:fqe-sharp-quadratic-variance` follows from the exact identity
`eq:fqe-qv-allstate-sos`, `2 D 𝔇(z) = Σ_{k,i} q_ki ‖Φ_ki(z)‖²_{w_{p_k}}` with an integer `D > 0` and positive integer
weights `q_ki` (95 covariants `Φ_ki = W_{a_k,p_k} v_ki`), because every summand is nonnegative.

* `QVCertIdentity`: the polynomial identity, as a `Prop`; it is proved in `QVCheck.Unconditional`
  (`QVCert.qvCertIdentity`) by an exact integer certificate check (layers `QVBlock`, `QVFrame`, `QVCheck`).
* `defectD_nonneg_of_certIdentity`: the certificate identity implies `𝔇 ≥ 0`.
* `sharpQV_of_certIdentity`: the certificate identity implies (QV).
-/

namespace FormalResearch.FourQubitEntropy.QVCert

/-- **The certificate identity** `eq:fqe-qv-allstate-sos`: `2 D 𝔇(z) = Σ_{k,i} q_ki ‖Φ_ki(z)‖²_{w_{p_k}}`
for all `z`, with `D = certD`, `q_ki` the 95 integer weights of `Data.lean` and `Φ_ki` the covariants of
`Covariants.lean`. -/
def QVCertIdentity : Prop :=
  ∀ z : Psi, 2 * (certD : ℝ) * defectD z
    = ∑ k : Fin 14, ∑ i ∈ Finset.range (blk k).weights.length, ((blk k).q i : ℝ) * (blk k).normSqPhi z i

/-- Every summand `q_ki ‖Φ_ki(z)‖²_w` is nonnegative. -/
theorem summand_nonneg (k : Fin 14) (z : Psi) (i : ℕ) (hi : i < (blk k).weights.length) :
    0 ≤ ((blk k).q i : ℝ) * (blk k).normSqPhi z i :=
  mul_nonneg (by exact_mod_cast (weights_pos k i hi).le) ((blk k).normSqPhi_nonneg z i)

/-- The certificate identity gives `𝔇 ≥ 0` on every vector. -/
theorem defectD_nonneg_of_certIdentity (h : QVCertIdentity) (z : Psi) : 0 ≤ defectD z := by
  have hD : (0 : ℝ) < 2 * certD := by norm_num [certD]
  have hsum : 0 ≤ 2 * (certD : ℝ) * defectD z := by
    rw [h z]
    exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i hi =>
      summand_nonneg k z i (Finset.mem_range.1 hi)
  exact (mul_nonneg_iff_of_pos_left hD).1 hsum

open FormalResearch.FourQubitEntropy.RenyiFull in
/-- **(QV) from the certificate identity**, `thm:fqe-sharp-quadratic-variance`. -/
theorem sharpQV_of_certIdentity (h : QVCertIdentity) : SharpQuadraticVarianceBound := by
  intro ψ hψ
  have h1 := defectD_nonneg_of_certIdentity h ψ
  rw [defectD_unit hψ] at h1
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.QVCert.sharpQV_of_certIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sharpQV_of_certIdentity

end FormalResearch.FourQubitEntropy.QVCert
