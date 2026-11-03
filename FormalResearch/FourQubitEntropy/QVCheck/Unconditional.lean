module

public import FormalResearch.FourQubitEntropy.QVCheck.Certify
public import FormalResearch.FourQubitEntropy.QVCert.Reduction
public import FormalResearch.FourQubitEntropy.RenyiFullHeadlineQV
public import FormalResearch.FourQubitEntropy.RenyiFullStateEq
public import FormalResearch.FourQubitEntropy.PaperEGenJointPurity

/-!
# (QV), (QK) and their consequences, unconditionally

* `QVCert.qvCertIdentity`: `2 D 𝔇(z) = Σ q_ki ‖Φ_ki(z)‖²_w` for all `z`, from `QVCheck.checkAll_true`
  (`eq:fqe-qv-allstate-sos`).
* `RenyiFull.sharpQuadraticVarianceBound`: (QV), `thm:fqe-sharp-quadratic-variance`.
* `RenyiFull.quadraticVarianceBound`: (QK), `thm:fqe-quadratic-variance`.
* Unconditional forms of the Paper E results that take (QK) or (QV) as a hypothesis (the conditional statements remain
  in their modules): `RenyiFull.renyi_envelope_above_one_unconditional` (`cor:fqe-renyi-gw` for `q > 1`),
  `joint_purity_unconditional` (`thm:fqe-joint-purity`), `RenyiFull.relaxTriple_of_state_unconditional`,
  `RenyiFull.meanRenyi_envelope_unconditional`, `RenyiFull.meanRenyi_envelope_eq_hs_unconditional`.

Trust: the axioms of every theorem here are `propext`, `Classical.choice`, `Quot.sound`, and `native_decide` for the
checker run `QVCheck.checkAll_true` and for the fact `QVCheck.cArr_rowC` (the checker's array `C` is the Lean-defined
six-copy intertwiner `QVCert.rowC`).
-/

@[expose] public section


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

/-- The three cut spectra of every unit vector form a triple of the classical relaxation (unconditionally). -/
theorem relaxTriple_of_state_unconditional {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    RelaxTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) :=
  relaxTriple_of_state quadraticVarianceBound hψ

/-- The classical relaxation `thm:fqe-renyi-classical` (every per-spectrum certificate is proved). -/
theorem classicalRelaxation : ClassicalRelaxation :=
  classical_relaxation hsSupporting (rationalDual_of_heads smallHeadDual largeHeadDual) cappedCubic
    clusterSliver

/-- **`cor:fqe-renyi-gw`, `q > 1`, with equality clauses on the cut spectra**, unconditionally
(`meanRenyi_envelope` with `ClassicalRelaxation` and (QK) discharged). -/
theorem meanRenyi_envelope_unconditional {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  meanRenyi_envelope classicalRelaxation quadraticVarianceBound hψ hq

/-- **Equality below the crossing**, unconditionally: if `h_q > 5/3` and `E_q(ψ) = h_q` then `ψ` is LU-equivalent
to `M₄` or `conj M₄`. -/
theorem meanRenyi_envelope_eq_hs_unconditional {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q)
    (hgt : 5 / 3 < hsRenyi q) (heq : meanRenyi q ψ = hsRenyi q) :
    LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  meanRenyi_envelope_eq_hs classicalRelaxation quadraticVarianceBound hψ hq hgt heq

end FormalResearch.FourQubitEntropy.RenyiFull

namespace FormalResearch.FourQubitEntropy

/-- **(JV), `thm:fqe-joint-purity`**, unconditionally: for every unit four-qubit vector,
`T + Σ_j p_j² ≤ 3P - 9/4` (`joint_purity_of_QK` with (QK) discharged). -/
theorem joint_purity_unconditional (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    cubicMoment ψ + (cutPurity12 ψ ^ 2 + cutPurity13 ψ ^ 2 + cutPurity14 ψ ^ 2)
      ≤ 3 * purity ψ - 9 / 4 :=
  joint_purity_of_QK ψ hψ (RenyiFull.quadraticVarianceBound ψ hψ)

end FormalResearch.FourQubitEntropy

/-! ### Axiom guards

The only axioms beyond `propext`, `Classical.choice`, `Quot.sound` are the two `native_decide` facts `QVCheck.checkAll_true` (the
checker run) and `QVCheck.cArr_rowC` (the checker's `C` is `QVCert.rowC`). -/

/-- info: 'FormalResearch.FourQubitEntropy.QVCert.qvCertIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms QVCert.qvCertIdentity

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.sharpQuadraticVarianceBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.sharpQuadraticVarianceBound

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.quadraticVarianceBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.quadraticVarianceBound

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.renyi_envelope_above_one_unconditional

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.relaxTriple_of_state_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.relaxTriple_of_state_unconditional

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.classicalRelaxation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.classicalRelaxation

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.meanRenyi_envelope_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.meanRenyi_envelope_unconditional

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.meanRenyi_envelope_eq_hs_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms RenyiFull.meanRenyi_envelope_eq_hs_unconditional

/-- info: 'FormalResearch.FourQubitEntropy.joint_purity_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_purity_unconditional

/-- info: 'QVCheck.checkAll_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Certify.0.QVCheck.checkAll_true._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms QVCheck.checkAll_true

/-- info: 'QVCheck.cArr_rowC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.FormalResearch.FourQubitEntropy.QVCheck.Intertwiner.0.QVCheck.cArr_rowC._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms QVCheck.cArr_rowC
