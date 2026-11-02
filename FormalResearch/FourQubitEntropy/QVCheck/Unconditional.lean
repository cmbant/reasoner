import FormalResearch.FourQubitEntropy.QVCheck.Certify
import FormalResearch.FourQubitEntropy.QVCert.Reduction
import FormalResearch.FourQubitEntropy.RenyiFullHeadlineQV

/-!
# The certificate identity, (QV), (QK) and the Rényi envelope above order one, unconditionally

* `QVCert.qvCertIdentity`: `2 D 𝔇(z) = Σ q_ki ‖Φ_ki(z)‖²_w` for all `z`, from `QVCheck.checkAll_true`.
* `RenyiFull.sharpQuadraticVarianceBound`: (QV), `thm:fqe-sharp-quadratic-variance`.
* `RenyiFull.quadraticVarianceBound`: (QK), `thm:fqe-quadratic-variance`.
* `RenyiFull.renyi_envelope_above_one_unconditional`: `cor:fqe-renyi-gw` for `q > 1`.
-/

open scoped ComplexConjugate
open scoped Matrix
open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace FormalResearch.FourQubitEntropy.QVCert

/-- **The certificate identity** (Paper E, `eq:fqe-qv-allstate-sos`), from the checker. -/
theorem qvCertIdentity : QVCertIdentity := by
  intro z
  have h1 := cert_diff_eq_qf (fun k : Fin 14 => blk k) (fun k => (blk k).weights.length)
    (fun k i => (blk k).q i) certD z
  rw [qf_eq_dot, QVCheck.kfam_bilinear QVCheck.checkAll_true] at h1
  have h2 : ((2 * (certD : ℝ) * QVCert.defectD z : ℝ) : ℂ) =
      ((∑ k : Fin 14, ∑ i ∈ Finset.range (blk k).weights.length,
        ((blk k).q i : ℝ) * (blk k).normSqPhi z i : ℝ) : ℂ) := by
    push_cast
    exact sub_eq_zero.mp h1
  exact_mod_cast h2

#print axioms qvCertIdentity

end FormalResearch.FourQubitEntropy.QVCert

namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- **(QV), `thm:fqe-sharp-quadratic-variance`**, unconditionally. -/
theorem sharpQuadraticVarianceBound : SharpQuadraticVarianceBound :=
  QVCert.sharpQV_of_certIdentity QVCert.qvCertIdentity

/-- **(QK), `thm:fqe-quadratic-variance`**, unconditionally. -/
theorem quadraticVarianceBound : QuadraticVarianceBound :=
  quadraticVarianceBound_of_sharp sharpQuadraticVarianceBound

/-- **`cor:fqe-renyi-gw` for `q > 1`**, unconditionally. -/
theorem renyi_envelope_above_one_unconditional
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one_QV sharpQuadraticVarianceBound hψ hq

#print axioms renyi_envelope_above_one_unconditional

end FormalResearch.FourQubitEntropy.RenyiFull
