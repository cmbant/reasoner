import FormalResearch.FourQubitEntropy.QVCheck.Hcheck
import FormalResearch.FourQubitEntropy.QVBlock.IntCert
import FormalResearch.FourQubitEntropy.QVFrame.FinalQV

/-!
# The certificate identity from the checker
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

theorem checkAll_all (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true) :
    checkChars () = true ∧ checkSlots () = true ∧ checkInv () = true ∧ checkPsi () = true ∧
    checkInvariant () = true ∧ checkPivots true = true ∧ checkPivots false = true := by
  unfold checkAll at hall
  simp only [Bool.and_eq_true] at hall
  exact ⟨hall.1.1.1.1.1.1.1.1.1.1.1.1, hall.1.1.1.1.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.1.1.1.1.2,
    hall.1.1.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.2⟩

/-- the bilinear form of `Kfam` vanishes on all `u^{⊗6}, v^{⊗6}` -/
theorem kfam_bilinear (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true) (z' z : Site → ℂ) :
    copyPower z' 6 ⬝ᵥ (((Kfam (fun k : Fin 14 => QVCert.blk k) (fun k => (QVCert.blk k).weights.length)
      (fun k i => (QVCert.blk k).q i) QVCert.certD).map (Int.castRingHom ℂ)) *ᵥ copyPower z 6) = 0 := by
  obtain ⟨hChars, hSlots, hInv, hPsi, hInvt, hPivV, hPivW⟩ := checkAll_all hall
  have key := quad_eq_zero_of_int_certificate (𝕜 := ℂ) (σ := Fin 2) (n := 6) (Q := Fin 4) (J := Spin)
    dimF (mult := multF) (fun j => by unfold dimF; omega) Cmat CinvMat DataStr.cDen cDen_ne
    (hCi_of_check hInv) (hiC_of_check hInv) gens wF hw_of rho0 (hrho0_of_check hSlots)
    Xk Xhk (hXk hSlots hPsi) nnF Vmat Wmat (fun p i => hV_of_check hInvt p i) (fun p i => hW_of_check hInvt p i)
    (fun p => Classical.choose (hdetV_of_check hPivV p)) (fun p => Classical.choose (hdetW_of_check hPivW p))
    (fun p => Classical.choose_spec (hdetV_of_check hPivV p))
    (fun p => Classical.choose_spec (hdetW_of_check hPivW p))
    (fun p => hchar_of_check hChars p) (fun p => hcheck_of_check hall p) z' z
  rw [Xsum] at key
  exact key

end QVCheck
