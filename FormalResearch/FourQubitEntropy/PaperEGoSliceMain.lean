module

public import FormalResearch.FourQubitEntropy.PaperEGoSliceConstr

/-!
# `thm:fqe-global-overlap`: the reduction `GOSliceCertificate → Q ≥ 1 - Φ`

`globalOverlap_of_slice`: the polynomial certificate on the 19-coordinate normal slice
(`GOSliceCertificate`, not proved in this file; its frame form is `go_frame_certificate` of `GOGlue/Final.lean`) implies `GlobalOverlap ψ` (`1 - Φ ≤ Q`) for every unit
`ψ`, given the three named reduction hypotheses

* `SliceQIdentity` (the polynomial identity `Q(Z(v)) = sliceQ v`, `eq:fqe-global-intrinsic` on the slice;
  proved as `sliceQIdentity`),
* `SliceNormalForm` (every unit state has a closest-point frame in slice form; proved as `sliceNormalForm`),
* `FrameHess` (the height Hessian is positive semidefinite at a closest point; proved as `frameHess`).

The positive constraints other than the Hessian are proved from `IsFrame` in `PaperEGoSliceConstr`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-- **Named hypothesis:** `Q` of the slice state is the slice polynomial `sliceQ`
(`eq:fqe-global-intrinsic` evaluated on `Z = √3 X + i Y`; checked numerically against the Python
`defects`, not proved in Lean). -/
def SliceQIdentity : Prop := ∀ v : SV, sexticQ (sState v) = sliceQ v

/-- **Named hypothesis:** every unit state `ψ` has a slice representative `sState v`, in the LU class
of `ψ` up to conjugation/phase (so same `Q` and `Φ`), at which `Z_*` is a closest point. -/
def SliceNormalForm : Prop :=
  ∀ ψ : Psi, normSqPsi ψ = 1 → ∃ (v : SV) (h : ℝ), IsFrame (sState v) h ∧
    sexticQ (sState v) = sexticQ ψ ∧ Phi ψ = h ^ 2

theorem globalOverlap_of_slice_conditional (cert : GOSliceCertificate) (hQ : SliceQIdentity)
    (hNF : SliceNormalForm) (hH : FrameHess) :
    ∀ ψ : Psi, normSqPsi ψ = 1 → GlobalOverlap ψ := by
  intro ψ hψ
  obtain ⟨v, h, hf, hq, hP⟩ := hNF ψ hψ
  have hc := frame_constraints hH hf
  have ht := cert v hc
  have hn : sN v = 1 := by rw [← normSqPsi_sState]; exact hf.1
  have h6 : sH0 v ^ 2 = 6 * h ^ 2 := by
    rw [hf.sH0_eq, mul_pow, Real.sq_sqrt (by norm_num)]
  unfold GlobalOverlap
  rw [hP, ← hq, hQ v]
  unfold sliceTarget sE at ht
  rw [hn, h6] at ht
  linarith

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.globalOverlap_of_slice_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalOverlap_of_slice_conditional

end

end FormalResearch.FourQubitEntropy.GO
