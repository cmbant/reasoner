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

`jb_fermions` restates, with the paper's constants, all three parts of the corollary:

* (i) `‖P (Ĝ F Ĝᵀ − U F Uᵀ) P‖ ≤ 3 C h^m`, and the same for the polar factor `Ũ = Ĝ (ĜᵀĜ)^{-1/2}`
  (`CFC.sqrt` formula of `jb_polar`) with `4 C h^m`;
* (ii) the `j`-th eigenvalues (`eigenvalues₀`, which Mathlib lists in decreasing order) of the compressions to
  the coordinates `e : m → n` differ by at most `3 C h^m`;
* (iii) for `0 < τ ≤ 1/2`, `6 C h^m ≤ τ` and `ν_j ∈ [τ, 1 − τ]` the entanglement energies differ by at
  most `9 C h^m / τ`.  The paper states `8 C h^m / τ` (`thmB.tex`, the mean-value bound on `[τ/2, 1 − τ/2]`); the
  constant `9` proved here is weaker, and the sharper `8` is not formalised.

All of it is derived from the Jacobi-operator package (`jop_fermion_compression_bound`,
`jop_fermion_eigenvalue_bound`, `jop_fermion_energy_bound`, `jop_polar_repair_matrix`); only the form of the
constants and the `CFC.sqrt` identification of the polar factor (via `jb_polar`) are new here.  The coordinate
projection is `P = diag p` with `p_i ∈ [0,1]` (a 0/1 projection is the special case).  `U` is any orthogonal
matrix; its identification with the Jacobi eigenvector matrix, the input `‖Ĝ − U‖ ≤ C h^m`
(Theorem B), the remark `rem:thb-entropy` and the Hermitian remark `rem:hermitian` are not formalised.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix FormalResearch.MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Free-fermion correlation matrices** (Paper J, `cor:fermions`), parts (i)-(iii), for the matrix `G = Ĝ_m`
with `‖G − U‖ ≤ C h^m < 1`.  Clause (i) is the compression bound for `G` (`3 C h^m`) and for the polar
factor (`4 C h^m`); clause (ii) is the eigenvalue comparison and (iii) the entanglement-energy comparison. -/
theorem jb_fermions (G U : Matrix n n ℝ) (f p : n → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hU : Uᵀ * U = 1)
    {C h : ℝ} {m : ℕ} (hGU : ‖G - U‖ ≤ C * h ^ m) (hC : C * h ^ m < 1) :
    ‖diagonal p * (G * diagonal f * Gᵀ - U * diagonal f * Uᵀ) * diagonal p‖ ≤ 3 * (C * h ^ m) ∧
    (∃ Q : Matrix n n ℝ, Q = G * (CFC.sqrt (Gᵀ * G))⁻¹ ∧ Qᵀ * Q = 1 ∧
      ‖diagonal p * (Q * diagonal f * Qᵀ - U * diagonal f * Uᵀ) * diagonal p‖ ≤ 4 * (C * h ^ m)) ∧
    (∀ {m' : Type*} [Fintype m'] [DecidableEq m'] (e : m' → n) (_ : Function.Injective e)
        (k : Fin (Fintype.card m')),
      |((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k -
          ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k| ≤ 3 * (C * h ^ m) ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → 6 * (C * h ^ m) ≤ τ →
        ((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k ∈ Set.Icc τ (1 - τ) →
        |Real.log ((1 - ((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k) /
              ((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k) -
          Real.log ((1 - ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k) /
              ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k)| ≤ 9 * (C * h ^ m) / τ) := by
  have hε0 : 0 ≤ C * h ^ m := (norm_nonneg _).trans hGU
  have hlt : ‖G - U‖ < 1 := hGU.trans_lt hC
  refine ⟨(jop_fermion_compression_bound G U f p hf hp hU hGU hC.le).1.trans
      (jop_fermion_compression_bound G U f p hf hp hU hGU hC.le).2, ?_, ?_⟩
  · obtain ⟨hG, hQo, -, -, hQU, -, -⟩ := jb_polar G U hU hlt
    set Q : Matrix n n ℝ := G * (CFC.sqrt (Gᵀ * G))⁻¹ with hQdef
    refine ⟨Q, rfl, hQo, ?_⟩
    have hQU' : ‖Q - U‖ ≤ 2 * (C * h ^ m) := by linarith
    have hprod := jop_fermion_product_bound Q U f hf hU hQU'
    have hQn := jop_norm_orth_le hQo
    refine (jop_compress_le p hp _).trans (hprod.trans ?_)
    nlinarith
  · intro m' _ _ e he k
    refine ⟨?_, fun τ hτ0 hτ hτ6 hν => ?_⟩
    · exact jop_fermion_eigenvalue_bound e he G U f hf hU hGU hC.le k
    · exact (jop_fermion_energy_bound e he G U f hf hU hGU hτ0 hτ6 hτ k).2 hν

/-- info: 'FormalResearch.JB.jb_fermions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_fermions

end FormalResearch.JB
