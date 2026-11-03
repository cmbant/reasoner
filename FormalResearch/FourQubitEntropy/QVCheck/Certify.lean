module

public import FormalResearch.FourQubitEntropy.QVCheck.Certificate
meta import QVCheckImpl.Impl5

/-!
# The checker run on the certificate (`native_decide`)

`QVCheck.checkAll` is the computable (Mathlib-free, precompiled) checker of `QVCheckImpl`.  This is the single
heavy computation of the whole certificate; its semantics is `QVCheck.kfam_bilinear` (all hypotheses of
`QVBlock.quad_eq_zero_of_int_certificate` are discharged from the `true`).
-/

@[expose] public section


namespace QVCheck

/-- **The finite certificate check passes** on the blocks of `QVCert.Data` and the right-hand side of `QVFrame.Defect`
(exact integer arithmetic; trusts the Lean compiler and the precompiled checker library, via `native_decide`). -/
theorem checkAll_true : checkAll blocksQ rhsTermsQ DataStr.certDen () = true := by
  native_decide

end QVCheck
