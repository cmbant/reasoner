import FormalResearch.FourQubitEntropy.PaperEGoSliceFinal

/-!
# GO glue: `thm:fqe-global-overlap` from the polynomial certificate at closest-point frames

`GOFrameCertificate`: `(Q - n² e)/36 ≥ 0` at every closest-point frame in slice form.  It is what the
symmetrised certificate proves: the constraints are needed only at frames, and the 48 coordinate maps
of the certificate map frames to frames (`GOGlue/OrbitMaps.lean`), so no closure of the constraint
set under the group is required.  `globalOverlap_of_frame_cert` is `globalOverlap_of_slice_conditional`
with the Hessian, normal form and `Q`-identity discharged and the interface weakened from
`GOSliceCertificate` to `GOFrameCertificate`.  Claim class: proved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace FormalResearch.FourQubitEntropy.GO
open CO OD

/-- The certificate at closest-point frames. -/
def GOFrameCertificate : Prop := ∀ (v : SV) (h : ℝ), IsFrame (sState v) h → 0 ≤ sliceTarget v

theorem GOSliceCertificate.frame (cert : GOSliceCertificate) : GOFrameCertificate :=
  fun v h hf => cert v (frame_constraints frameHess hf)

theorem globalOverlap_of_frame_cert (cert : GOFrameCertificate) :
    ∀ ψ : Psi, normSqPsi ψ = 1 → GlobalOverlap ψ := by
  intro ψ hψ
  obtain ⟨v, h, hf, hq, hP⟩ := sliceNormalForm ψ hψ
  have ht := cert v h hf
  have hn : sN v = 1 := by rw [← normSqPsi_sState]; exact hf.1
  have h6 : sH0 v ^ 2 = 6 * h ^ 2 := by
    rw [hf.sH0_eq, mul_pow, Real.sq_sqrt (by norm_num)]
  unfold GlobalOverlap
  rw [hP, ← hq, sliceQIdentity v]
  unfold sliceTarget sE at ht
  rw [hn, h6] at ht
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.GO.globalOverlap_of_frame_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalOverlap_of_frame_cert

end FormalResearch.FourQubitEntropy.GO
