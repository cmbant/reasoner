import FormalResearch.FourQubitEntropy.QVCheck.Unconditional

/-!
# (QV), (QK) and the Rényi envelope above order one: aggregate

The unconditional proof of the certificate identity `2 D 𝔇(z) = Σ q_ki ‖Φ_ki(z)‖²_w` (`QVCert.qvCertIdentity`), hence of
(QV) `RenyiFull.sharpQuadraticVarianceBound`, (QK) `RenyiFull.quadraticVarianceBound` and
`RenyiFull.renyi_envelope_above_one_unconditional`, is organised in layers; `QVCheck.Unconditional` is the entry point.

* `QVCert` (statement): the certificate data, the covariants `Φ_ki`, weighted norms and the reduction of (QV) to the
  identity (`QVCert.Reduction`).
* `QVBlock` (generic, no data): from finitely many integer matrix identities to `⟨u^{⊗n}, K v^{⊗n}⟩ = 0`
  (`QVBlock.quad_eq_zero_of_int_certificate`).
* `QVFrame` (generic, no certificate data): the identity as a quadratic form in `z^{⊗6}`, `2 D 𝔇 - Σ q ‖Φ‖² = ⟨z^{⊗6}, K z^{⊗6}⟩`
  (`QVFrame.cert_diff_eq_qf`).
* `QVCheckImpl` (repository root, Mathlib-free, precompiled): the executable checker `checkAll` and its data.
* `QVCheck` (this directory): the semantics of the checker, in the order `Arrays`, `Coupling`, `Invariants`, `Intertwiner`,
  `Coupled`, `Terms`, `Placement`, `Sector`, `Bridge`, `Certificate` (`kfam_bilinear`: `checkAll … = true` implies the bilinear
  form of `K` vanishes), then `Certify` (`checkAll_true`, by `native_decide`) and `Unconditional`.
-/
