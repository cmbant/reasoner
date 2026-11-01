import FormalResearch.FourQubitEntropy.QVFrame.Final
import FormalResearch.FourQubitEntropy.QVCert.Reduction

/-!
# `QVCertIdentity` from `P K P = 0`

`qvCertIdentity_of_symmetrised`: for the data of `Data.lean`, `P K P = 0` for
`K = Kfam blk cnt q certD` (`P = QVBlock.copySym`, the `S_6` copy-symmetriser) implies `QVCertIdentity`.
This is the interface to the block calculus of `QVBlock` (`copySym_mul_sum_mul_copySym_eq_zero`).
Only this file imports `QVCert.Reduction`; it must be updated if the block count `Fin 14` changes.
-/

open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

open QVCert in
/-- The certificate identity follows from `P K P = 0` for `K = 2 D K_RHS - Σ q_{ki} A^{(6)}_{ki}`
(the data of `Data.lean`; `QVBlock.copySym` is the `S_6` copy-symmetriser). -/
theorem qvCertIdentity_of_symmetrised
    (h : copySym ℂ (Fin 4) (Fin 2) 6 *
        (Kfam (fun k : Fin 14 => blk k) (fun k => (blk k).weights.length) (fun k i => (blk k).q i) certD).map
          (Int.castRingHom ℂ) * copySym ℂ (Fin 4) (Fin 2) 6 = 0) :
    QVCertIdentity := by
  intro z
  have h1 := cert_diff_eq_qf (fun k : Fin 14 => blk k) (fun k => (blk k).weights.length)
    (fun k i => (blk k).q i) certD z
  rw [qf_eq_dot, bilin_eq_zero_of_symmetrised _ h] at h1
  have h2 : ((2 * (certD : ℝ) * QVCert.defectD z : ℝ) : ℂ) =
      ((∑ k : Fin 14, ∑ i ∈ Finset.range (blk k).weights.length,
        ((blk k).q i : ℝ) * (blk k).normSqPhi z i : ℝ) : ℂ) := by
    push_cast
    exact sub_eq_zero.mp h1
  exact_mod_cast h2

end FormalResearch.FourQubitEntropy.QVFrame
