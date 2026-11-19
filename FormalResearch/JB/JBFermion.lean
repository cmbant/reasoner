module

public import Mathlib
public import FormalResearch.JB.JBDefs
public import FormalResearch.JB.JBPolar
public import FormalResearch.MatrixAnalysis.JacobiOpFermions

/-!
# Paper J, Theorem B reduction: free-fermion correlation matrices (`cor:fermions`)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/main_results.tex` (`cor:fermions`; proof in `thmB.tex`),
on branch `agents/m7-m1-global-racah` of QIprojects.  The paper's constants are `ε = C_m h^m` (the hypothesis `‖Ĝ_m − U_h‖ ≤ C_m h^m`, Theorem B),
and `ε = 2 C_m h^m` for the polar factor.

`FermionConcl G U ε` is the conclusion of the corollary for a matrix `G` (the paper's `Ĝ_m`) with `‖G − U‖ ≤ ε`, `U` orthogonal:

* (i) for every real matrix `F` with `‖F‖ ≤ 1` and every orthogonal projection `P` (`Pᵀ = P`, `P P = P`, not necessarily a coordinate projection),
  `‖P (G F Gᵀ − U F Uᵀ) P‖ ≤ 3 ε`; and the same for the polar factor `Q = G (GᵀG)^{-1/2}` (`CFC.sqrt`, orthogonal) with `4 ε`;
* (ii) for every orthonormal basis of the range of a projection (an isometry `J : n → m'`, `Jᵀ J = 1`, so that `J Jᵀ` is the projection and `Jᵀ M J` the compression of `M` to its range, as a matrix on `m'`)
  and every symmetric `F` with `‖F‖ ≤ 1`, the `k`-th eigenvalues (`eigenvalues₀`, which Mathlib lists in decreasing order) of the compressions of `U F Uᵀ` and `G F Gᵀ` differ by at most `3 ε`;
* (iii) for `0 < τ ≤ 1/2`, `6 ε ≤ τ` and `ν_k ∈ [τ, 1 − τ]` the entanglement energies `log((1−ν)/ν)` differ by at most `8 ε / τ`, the paper's constant
  (`thmB.tex`, the mean value bound on `[τ/2, 1 − τ/2]`, where the energy is `8/(3τ)`-Lipschitz and `|ν_k − ν̂_k| ≤ 3 ε`).

`jb_fermions : ‖G − U‖ ≤ ε < 1 → FermionConcl G U ε` is proved from the Jacobi-operator package (`jop_entanglement_energy_bound`, `jb_polar`) and the bounds `jbf_*` below (general `F`, `P`, `J`).

## Differences from the paper

* Real matrices: the paper allows a complex `F` (and complex projections); here `F`, `P`, `J` are real.  The hypothesis of (ii), (iii) is `F` symmetric with `‖F‖ ≤ 1` (the paper: `0 ≤ F ≤ I`); `ν_k ∈ (0,1)` is not needed
  as a hypothesis since `ν̂_k ∈ [τ/2, 1 − τ/2]` follows from `|ν_k − ν̂_k| ≤ 3ε ≤ τ/2`.
* The bound `(2+δ)δ` of the paper's first display is stated through `3 ε` (`δ < 1`).
* `U` is any orthogonal matrix; its identification with the Jacobi eigenvector matrix, the input `‖Ĝ − U‖ ≤ C h^m` (Theorem B), the remark `rem:thb-entropy` and the Hermitian remark `rem:hermitian` are not formalised.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix FormalResearch.MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `‖G F Gᵀ − U F Uᵀ‖ ≤ ε (‖G‖ + 1)` for `‖F‖ ≤ 1` (the general-`F` form of `jop_fermion_product_bound`). -/
lemma jbf_product_bound (G U F : Matrix n n ℝ) (hF : ‖F‖ ≤ 1) (hU : Uᵀ * U = 1) {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) :
    ‖G * F * Gᵀ - U * F * Uᵀ‖ ≤ ε * (‖G‖ + 1) := by
  have hid : G * F * Gᵀ - U * F * Uᵀ = (G - U) * F * Gᵀ + U * F * (G - U)ᵀ := by
    simp only [Matrix.transpose_sub]; noncomm_ring
  have hε : 0 ≤ ε := (norm_nonneg _).trans hGU
  have hT : ‖(G - U)ᵀ‖ ≤ ε := by rwa [jop_norm_transpose]
  have h1 : ‖(G - U) * F * Gᵀ‖ ≤ ε * 1 * ‖G‖ := by
    calc _ ≤ ‖(G - U) * F‖ * ‖Gᵀ‖ := l2_opNorm_mul _ _
      _ ≤ (‖G - U‖ * ‖F‖) * ‖Gᵀ‖ := by gcongr; exact l2_opNorm_mul _ _
      _ ≤ ε * 1 * ‖G‖ := by rw [jop_norm_transpose]; gcongr
  have h2 : ‖U * F * (G - U)ᵀ‖ ≤ 1 * 1 * ε := by
    calc _ ≤ ‖U * F‖ * ‖(G - U)ᵀ‖ := l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖F‖) * ‖(G - U)ᵀ‖ := by gcongr; exact l2_opNorm_mul _ _
      _ ≤ 1 * 1 * ε := by gcongr; exact jop_norm_orth_le hU
  rw [hid]
  calc _ ≤ ‖(G - U) * F * Gᵀ‖ + ‖U * F * (G - U)ᵀ‖ := norm_add_le _ _
    _ ≤ ε * (‖G‖ + 1) := by nlinarith

/-- An orthogonal projection has norm at most `1`. -/
lemma jbf_norm_proj_le {P : Matrix n n ℝ} (hT : Pᵀ = P) (h2 : P * P = P) : ‖P‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self P
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hT, h2] at h
  nlinarith [norm_nonneg P]

/-- Compression by a contraction: `‖P M P‖ ≤ ‖M‖` for `‖P‖ ≤ 1`. -/
lemma jbf_compress_le (P M : Matrix n n ℝ) (hP : ‖P‖ ≤ 1) : ‖P * M * P‖ ≤ ‖M‖ := by
  calc _ ≤ ‖P * M‖ * ‖P‖ := l2_opNorm_mul _ _
    _ ≤ (‖P‖ * ‖M‖) * ‖P‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by gcongr
    _ = ‖M‖ := by ring

section Isometry

variable {m' : Type*} [Fintype m'] [DecidableEq m']

/-- An isometry `J` (`Jᵀ J = 1`) has norm at most `1`. -/
lemma jbf_norm_isometry_le (J : Matrix n m' ℝ) (hJ : Jᵀ * J = 1) : ‖J‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self J
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hJ] at h
  have h1 : ‖(1 : Matrix m' m' ℝ)‖ ≤ 1 := by
    have := jop_norm_diagonal_le (fun _ : m' => (1 : ℝ)) zero_le_one fun _ => by simp
    simpa using this
  nlinarith [norm_nonneg J]

/-- Compression to the range of an isometry does not increase the norm. -/
lemma jbf_compress_iso_le (J : Matrix n m' ℝ) (hJ : Jᵀ * J = 1) (M : Matrix n n ℝ) : ‖Jᵀ * M * J‖ ≤ ‖M‖ := by
  have hJn := jbf_norm_isometry_le J hJ
  have hJt : ‖Jᵀ‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose J
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [h]; exact hJn
  calc _ ≤ ‖Jᵀ * M‖ * ‖J‖ := l2_opNorm_mul _ _
    _ ≤ (‖Jᵀ‖ * ‖M‖) * ‖J‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by gcongr
    _ = ‖M‖ := by ring

/-- `G F Gᵀ` is Hermitian for symmetric `F`. -/
lemma jbf_sandwich_isHermitian (G F : Matrix n n ℝ) (hF : Fᵀ = F) : (G * F * Gᵀ).IsHermitian := by
  have hd : F.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hF
  simpa using Matrix.isHermitian_mul_mul_conjTranspose G hd

/-- The compression `Jᵀ M J` of a Hermitian matrix is Hermitian. -/
lemma jbf_compress_isHermitian (J : Matrix n m' ℝ) {M : Matrix n n ℝ} (hM : M.IsHermitian) : (Jᵀ * M * J).IsHermitian := by
  simpa using Matrix.isHermitian_conjTranspose_mul_mul J hM

/-- **Weyl for the compressions** (cor:fermions (ii)): the `k`-th eigenvalues of `Jᵀ (U F Uᵀ) J` and `Jᵀ (G F Gᵀ) J` differ by at most `3 ε`. -/
lemma jbf_eigenvalue_bound (J : Matrix n m' ℝ) (hJ : Jᵀ * J = 1) (G U F : Matrix n n ℝ) (hF : Fᵀ = F) (hF1 : ‖F‖ ≤ 1)
    (hU : Uᵀ * U = 1) {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) (hε1 : ε ≤ 1) (k : Fin (Fintype.card m')) :
    |(jbf_compress_isHermitian J (jbf_sandwich_isHermitian U F hF)).eigenvalues₀ k -
        (jbf_compress_isHermitian J (jbf_sandwich_isHermitian G F hF)).eigenvalues₀ k| ≤ 3 * ε := by
  refine (Spectral.herm_abs_eigenvalues₀_sub_le_norm _ _ k).trans ?_
  have e : Jᵀ * (U * F * Uᵀ) * J - Jᵀ * (G * F * Gᵀ) * J = -(Jᵀ * (G * F * Gᵀ - U * F * Uᵀ) * J) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [e, norm_neg]
  refine (jbf_compress_iso_le J hJ _).trans ((jbf_product_bound G U F hF1 hU hGU).trans ?_)
  have := jop_norm_G_le hU hGU
  have : 0 ≤ ε := (norm_nonneg _).trans hGU
  nlinarith

end Isometry

/-- **The conclusion of `cor:fermions`** for `G` with `‖G − U‖ ≤ ε`: see the module docstring, clauses (i)--(iii). -/
def FermionConcl (G U : Matrix n n ℝ) (ε : ℝ) : Prop :=
  (∀ F P : Matrix n n ℝ, ‖F‖ ≤ 1 → Pᵀ = P → P * P = P → ‖P * (G * F * Gᵀ - U * F * Uᵀ) * P‖ ≤ 3 * ε) ∧
  (∃ Q : Matrix n n ℝ, Q = G * (CFC.sqrt (Gᵀ * G))⁻¹ ∧ Qᵀ * Q = 1 ∧
    ∀ F P : Matrix n n ℝ, ‖F‖ ≤ 1 → Pᵀ = P → P * P = P → ‖P * (Q * F * Qᵀ - U * F * Uᵀ) * P‖ ≤ 4 * ε) ∧
  (∀ (m' : Type) [Fintype m'] [DecidableEq m'] (J : Matrix n m' ℝ), Jᵀ * J = 1 →
    ∀ F : Matrix n n ℝ, ∀ hF : Fᵀ = F, ‖F‖ ≤ 1 → ∀ k : Fin (Fintype.card m'),
      |(jbf_compress_isHermitian J (jbf_sandwich_isHermitian U F hF)).eigenvalues₀ k -
          (jbf_compress_isHermitian J (jbf_sandwich_isHermitian G F hF)).eigenvalues₀ k| ≤ 3 * ε ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → 6 * ε ≤ τ →
        (jbf_compress_isHermitian J (jbf_sandwich_isHermitian U F hF)).eigenvalues₀ k ∈ Set.Icc τ (1 - τ) →
        |Real.log ((1 - (jbf_compress_isHermitian J (jbf_sandwich_isHermitian U F hF)).eigenvalues₀ k) /
              (jbf_compress_isHermitian J (jbf_sandwich_isHermitian U F hF)).eigenvalues₀ k) -
          Real.log ((1 - (jbf_compress_isHermitian J (jbf_sandwich_isHermitian G F hF)).eigenvalues₀ k) /
              (jbf_compress_isHermitian J (jbf_sandwich_isHermitian G F hF)).eigenvalues₀ k)| ≤ 8 * ε / τ)

/-- **Free-fermion correlation matrices** (Paper J, `cor:fermions`), parts (i)-(iii): for `U` orthogonal and `‖G − U‖ ≤ ε < 1` (`ε = C h^m` with the input `‖Ĝ_m − U_h‖ ≤ C h^m` of Theorem B),
`FermionConcl G U ε`.  Clause (i) is the compression bound for `G` (`3 ε`) and for the polar factor (`4 ε`); clause (ii) is the eigenvalue comparison and (iii) the entanglement-energy comparison (`8 ε / τ`). -/
theorem jb_fermions (G U : Matrix n n ℝ) (hU : Uᵀ * U = 1) {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) (hε : ε < 1) :
    FermionConcl G U ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hGU
  have hlt : ‖G - U‖ < 1 := hGU.trans_lt hε
  have hG := jop_norm_G_le hU hGU
  refine ⟨fun F P hF hPt hPP => ?_, ?_, fun m' _ _ J hJ F hF hF1 k => ?_⟩
  · refine (jbf_compress_le P _ (jbf_norm_proj_le hPt hPP)).trans ((jbf_product_bound G U F hF hU hGU).trans ?_)
    nlinarith
  · obtain ⟨-, hQo, -, -, hQU, -, -⟩ := jb_polar G U hU hlt
    set Q : Matrix n n ℝ := G * (CFC.sqrt (Gᵀ * G))⁻¹ with hQdef
    refine ⟨Q, rfl, hQo, fun F P hF hPt hPP => ?_⟩
    have hQU' : ‖Q - U‖ ≤ 2 * ε := by linarith
    have hQn := jop_norm_orth_le hQo
    refine (jbf_compress_le P _ (jbf_norm_proj_le hPt hPP)).trans ((jbf_product_bound Q U F hF hU hQU').trans ?_)
    nlinarith
  · refine ⟨jbf_eigenvalue_bound J hJ G U F hF hF1 hU hGU hε.le k, fun τ hτ0 hτ hτ6 hν => ?_⟩
    exact jop_entanglement_energy_bound hε0 hτ6 hτ hτ0 hν (jbf_eigenvalue_bound J hJ G U F hF hF1 hU hGU hε.le k)

/-- info: 'FormalResearch.JB.jb_fermions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_fermions

end FormalResearch.JB
