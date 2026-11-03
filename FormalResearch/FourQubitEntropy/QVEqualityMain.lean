module

public import FormalResearch.FourQubitEntropy.QVEqualityClassify
public import FormalResearch.FourQubitEntropy.QVEqualityRFMain
public import FormalResearch.FourQubitEntropy.QVCheck.Unconditional

/-!
# Equality in the quadratic variance bounds (Paper E): headline statements

* `thm:fqe-sharp-quadratic-variance` (QV): equality along the cluster-to-Bell family and sharpness of `3`
  (`QVEqualityFamily.lean`: `quadFam_qv_equality`, `quadFam_qv_ratio`, `qv_coefficient_optimal`); here the
  two-sided form `qv_coefficient_iff` (uses (QV)).
* `thm:fqe-quadratic-variance` (QK): the equality classification `qk_equality_classification`, the structural
  forms (`qk_equality_classification_product`), and optimality of the coefficients `9/2` and `6`
  (`qk_coefficient_nine_half_optimal`, `qk_coefficient_six_optimal`).
* `prop:fqe-critical-variance` (RF) at `P = 1`: `critical_rf` (`QVEqualityState.lean`), its equality case and
  attainment (`QVEqualityRFMain.lean`: `critical_rf_equality_iff`, `critical_rf_attained`, ...).

The `native_decide` axioms in the axiom lists of the QV-dependent theorems come only from the
certificate checker behind `RenyiFull.sharpQuadraticVarianceBound`; `qk_equality_iff` (in
`QVEqualityClassify.lean`) takes (QV) as a hypothesis.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

/-- **Equality classification in (QK)** (`thm:fqe-quadratic-variance`, unconditional): for a unit pure
four-qubit state, `F² + (9/2)(P - 1) = 6 V_P` iff the three cut spectra are, up to ordering of cuts and
eigenvalues, HS spectra, cluster spectra, or the spectra of a product of two Bell pairs. -/
theorem qk_equality_classification {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    6 * VP ψ = sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1) ↔
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) :=
  qk_equality_iff sharpQuadraticVarianceBound hψ

/-- The same with the structural form of the Bell case: `ψ` is a local-unitary image of a product of two
Bell pairs (`bell2`, `bell13`, `bell14`). -/
theorem qk_equality_classification_product {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    6 * VP ψ = sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1) ↔
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨ IsBellProduct ψ := by
  rw [qk_equality_classification hψ, isBellTriple_iff_bellProduct hψ]

/-- (QK) for a unit state, in the `VP` notation (restating `RenyiFull.quadraticVarianceBound`). -/
theorem qk_bound {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    6 * VP ψ ≤ sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1) := quadraticVarianceBound ψ hψ

/-- (QV) for a unit state, in the `VP` notation. -/
theorem qv_bound {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    6 * VP ψ ≤ sexticF ψ ^ 2 + 3 * purity ψ * (purity ψ - 1) := sharpQuadraticVarianceBound ψ hψ

/-! ### Optimality of the coefficients -/

theorem bell2_VP : normSqPsi bell2 = 1 ∧ purity bell2 = 3 / 2 ∧ sexticF bell2 = 0 ∧ VP bell2 = 3 / 8 := by
  have hxy : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  rw [bell2_eq_quadFam]
  refine ⟨quadFam_unit hxy, ?_, ?_, ?_⟩
  · rw [quadFam_purity_eq hxy]; norm_num
  · rw [quadFam_F_eq hxy]; norm_num
  · rw [quadFam_VP_eq hxy]; norm_num

/-- The cluster-type member of (QF), `x² = y² = 1/2`. -/
noncomputable def clusterQF : Psi := quadFam (Real.sqrt (1 / 2)) (Real.sqrt (1 / 2))

theorem clusterQF_VP : normSqPsi clusterQF = 1 ∧ purity clusterQF = 1 ∧ sexticF clusterQF = 1 / 2 ∧
    VP clusterQF = 1 / 24 := by
  have hx2 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hxy : (Real.sqrt (1 / 2)) ^ 2 + (Real.sqrt (1 / 2)) ^ 2 = 1 := by rw [hx2]; norm_num
  unfold clusterQF
  refine ⟨quadFam_unit hxy, ?_, ?_, ?_⟩
  · rw [quadFam_purity_eq hxy]; norm_num
  · rw [quadFam_F_eq hxy]; norm_num
  · rw [quadFam_VP_eq hxy]; norm_num

/-- **The coefficient `9/2` of (QK) cannot be decreased** (Bell-pair products). -/
theorem qk_coefficient_nine_half_optimal {c : ℝ}
    (h : ∀ ψ : Psi, normSqPsi ψ = 1 → 6 * VP ψ ≤ sexticF ψ ^ 2 + c * (purity ψ - 1)) : 9 / 2 ≤ c := by
  obtain ⟨h1, h2, h3, h4⟩ := bell2_VP
  have := h bell2 h1
  rw [h2, h3, h4] at this
  linarith

/-- **The coefficient `6` of (QK) cannot be increased while retaining `9/2`** (cluster spectra). -/
theorem qk_coefficient_six_optimal {a : ℝ}
    (h : ∀ ψ : Psi, normSqPsi ψ = 1 → a * VP ψ ≤ sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1)) : a ≤ 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := clusterQF_VP
  have := h clusterQF h1
  rw [h2, h3, h4] at this
  linarith

/-- **Sharpness of the coefficient `3` of (QV), two-sided**: `F² + c P (P-1) ≥ 6 V_P` holds for all unit
states iff `c ≥ 3`. -/
theorem qv_coefficient_iff {c : ℝ} :
    (∀ ψ : Psi, normSqPsi ψ = 1 → 6 * VP ψ ≤ sexticF ψ ^ 2 + c * purity ψ * (purity ψ - 1)) ↔ 3 ≤ c := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := bell2_VP
    have := h bell2 h1
    rw [h2, h3, h4] at this
    linarith
  · intro hc ψ hψ
    have h := qv_bound hψ
    have hP := purity_ge ψ
    rw [hψ] at hP
    have : 0 ≤ purity ψ * (purity ψ - 1) := mul_nonneg (by nlinarith) (by nlinarith)
    nlinarith

/-- All three equality types are attained, with the optimal coefficients: summary of the corollary's
sharpness clauses. -/
theorem qk_coefficients_sharp :
    (∀ c : ℝ, (∀ ψ : Psi, normSqPsi ψ = 1 → 6 * VP ψ ≤ sexticF ψ ^ 2 + c * (purity ψ - 1)) → 9 / 2 ≤ c) ∧
    (∀ a : ℝ, (∀ ψ : Psi, normSqPsi ψ = 1 → a * VP ψ ≤ sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1)) → a ≤ 6) :=
  ⟨fun _ h => qk_coefficient_nine_half_optimal h, fun _ h => qk_coefficient_six_optimal h⟩

end FormalResearch.FourQubitEntropy.QVEquality

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.quadFam_qv_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.quadFam_qv_equality

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.quadFam_qv_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.quadFam_qv_ratio

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.qv_coefficient_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.qv_coefficient_optimal

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_rf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_rf

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_qk_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_qk_equality

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.isBellTriple_iff_bellProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.isBellTriple_iff_bellProduct

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.qk_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.qk_equality_iff

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.qk_equality_classification' depends on axioms: [propext, Classical.choice, Quot.sound, QVCheck.cArr_rowC._native.native_decide.ax_1_1, QVCheck.checkAll_true._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.qk_equality_classification

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.qk_equality_classification_product' depends on axioms: [propext, Classical.choice, Quot.sound, QVCheck.cArr_rowC._native.native_decide.ax_1_1, QVCheck.checkAll_true._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.qk_equality_classification_product

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.qk_coefficients_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.qk_coefficients_sharp

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.qv_coefficient_iff' depends on axioms: [propext, Classical.choice, Quot.sound, QVCheck.cArr_rowC._native.native_decide.ax_1_1, QVCheck.checkAll_true._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.qv_coefficient_iff
