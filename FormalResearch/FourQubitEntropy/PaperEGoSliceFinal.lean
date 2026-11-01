import FormalResearch.FourQubitEntropy.PaperEGoSliceQId3
import FormalResearch.FourQubitEntropy.PaperEGoSliceHessQ

/-!
# `thm:fqe-global-overlap` from the slice certificate

`globalOverlap_of_slice : GOSliceCertificate → ∀ ψ, normSqPsi ψ = 1 → GlobalOverlap ψ`.
Proved: the coverage by the normal slice (`sliceNormalForm`), the positive constraints at a closest point
(`frame_constraints`, incl. `frameHess`), and the polynomial identity `sliceQIdentity`
(`sexticQ_psiZ`, `eq:fqe-global-intrinsic`).  The only input is the polynomial certificate
`GOSliceCertificate`.
-/

namespace FormalResearch.FourQubitEntropy.GO
open CO OD

theorem globalOverlap_of_slice (cert : GOSliceCertificate) :
    ∀ ψ : Psi, normSqPsi ψ = 1 → GlobalOverlap ψ :=
  globalOverlap_of_slice_cert cert sliceQIdentity

/-- info: 'FormalResearch.FourQubitEntropy.GO.globalOverlap_of_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalOverlap_of_slice

end FormalResearch.FourQubitEntropy.GO
