import FormalResearch.FourQubitEntropy.PaperEGoSliceQId

/-!
# `eq:fqe-global-intrinsic`: `Q` of the state with magic matrix `Z`

For every `Z : Mat4`, the state `ψ_Z` with magic coordinates `Z` has
`Q(ψ_Z) = -4 n³ + 27 n tr[(ZZ†)²] - 18 tr[(ZZ†)³] - 18 ‖Z Zᵀ Z - (tr ZᵀZ/2) Z‖²`, `n = ‖Z‖²`
(`sexticQ_psiZ`).  Proof by the adjugate route: `Q = 5 n³ - 36 C`, `C = Σ_cuts e₃(ρ_cut)`,
`e₃(M M†) = ‖adj M‖²`, and the entrywise cubic identities `adj M₁₃ = α₁₃(adj Z, N)`,
`adj M₁₄ = α₁₄(adj Z, N)` (`adj13_eq`, `adj14_eq`) with `Σ|α₁₃|² + Σ|α₁₄|² = ½(‖adj Z‖² + ‖N‖²)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-! ### Transport from `Fin 2 × Fin 2` to `Fin 4` -/

def toF (M : Mat4) : M4C := M.submatrix pairEquiv.symm pairEquiv.symm

theorem toF_mul (M N : Mat4) : toF (M * N) = toF M * toF N := by
  unfold toF
  rw [Matrix.submatrix_mul_equiv M N _ pairEquiv.symm _]

theorem toF_transpose (M : Mat4) : toF Mᵀ = (toF M)ᵀ := by
  unfold toF; rw [Matrix.transpose_submatrix]

theorem toF_adjugate (M : Mat4) : toF M.adjugate = (toF M).adjugate :=
  (Matrix.adjugate_submatrix_equiv_self pairEquiv.symm M).symm

theorem toF_trace (M : Mat4) : Matrix.trace (toF M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, toF, Matrix.submatrix_apply]
  exact Equiv.sum_comp pairEquiv.symm (fun p => M p p)

theorem sum_toF (f : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℝ) :
    ∑ i : Fin 4, ∑ j : Fin 4, f (pairEquiv.symm i) (pairEquiv.symm j) = ∑ p, ∑ q, f p q := by
  rw [Equiv.sum_comp pairEquiv.symm (fun p => ∑ j : Fin 4, f p (pairEquiv.symm j))]
  exact Finset.sum_congr rfl fun p _ => Equiv.sum_comp pairEquiv.symm (f p)

theorem pe0 : pairEquiv.symm (0 : Fin 4) = ((0 : Fin 2), (0 : Fin 2)) := by
  rw [Equiv.symm_apply_eq]; rfl
theorem pe1 : pairEquiv.symm (1 : Fin 4) = ((0 : Fin 2), (1 : Fin 2)) := by
  rw [Equiv.symm_apply_eq]; rfl
theorem pe2 : pairEquiv.symm (2 : Fin 4) = ((1 : Fin 2), (0 : Fin 2)) := by
  rw [Equiv.symm_apply_eq]; rfl
theorem pe3 : pairEquiv.symm (3 : Fin 4) = ((1 : Fin 2), (1 : Fin 2)) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem toF_B : toF magicB = rt • Bp := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toF, magicB, Bp, pe0, pe1, pe2, pe3] <;> ring

/-- The state with magic coordinates `Z`. -/
def psiZ (Z : Mat4) : Psi := ofZmat (magicB * Z * magicBᵀ)

theorem zmat_psiZ (Z : Mat4) : zmat (psiZ Z) = magicB * Z * magicBᵀ := by
  unfold psiZ; exact zmat_ofZmat _

theorem toF_zmat_psiZ (Z : Mat4) : toF (zmat (psiZ Z)) = Wf (toF Z) := by
  rw [zmat_psiZ, toF_mul, toF_mul, toF_transpose, toF_B]
  unfold Wf
  rw [Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, rt_mul_rt]

def cut13 (ψ : Psi) : Mat4 := Matrix.of fun i j => ψ i.1 j.1 i.2 j.2
def cut14 (ψ : Psi) : Mat4 := Matrix.of fun i j => ψ i.1 j.1 j.2 i.2

theorem toF_cut13 (Z : Mat4) : toF (cut13 (psiZ Z)) = M13f (toF Z) := by
  have h := toF_zmat_psiZ Z
  ext i j
  have := congrFun (congrFun h (r13 i j)) (c13 i j)
  unfold M13f
  rw [Matrix.of_apply, ← this]
  fin_cases i <;> fin_cases j <;>
    simp [toF, cut13, zmat, r13, c13, pe0, pe1, pe2, pe3]

theorem toF_cut14 (Z : Mat4) : toF (cut14 (psiZ Z)) = M14f (toF Z) := by
  have h := toF_zmat_psiZ Z
  ext i j
  have := congrFun (congrFun h (r13 i j)) (c14 i j)
  unfold M14f
  rw [Matrix.of_apply, ← this]
  fin_cases i <;> fin_cases j <;>
    simp [toF, cut14, zmat, r13, c14, pe0, pe1, pe2, pe3]

/-! ### Reduced matrices as Gram matrices -/

theorem red12_eq (ψ : Psi) : red12 ψ = zmat ψ * (zmat ψ)ᴴ := by
  ext i j
  simp [red12, zmat, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Complex.star_def]

theorem red13_eq (ψ : Psi) : red13 ψ = cut13 ψ * (cut13 ψ)ᴴ := by
  ext i j
  simp [red13, cut13, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Complex.star_def]

theorem red14_eq (ψ : Psi) : red14 ψ = cut14 ψ * (cut14 ψ)ᴴ := by
  ext i j
  simp [red14, cut14, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Complex.star_def]

theorem trace_conjTranspose_mul_self (M : Mat4) :
    Matrix.trace (Mᴴ * M) = ((∑ p, ∑ q, Complex.normSq (M p q) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  exact Finset.sum_comm

/-- `e₃(M M†) = ‖adj M‖²`. -/
theorem trace_adj_gram (M : Mat4) :
    Matrix.trace (M * Mᴴ).adjugate = ((∑ p, ∑ q, Complex.normSq (M.adjugate p q) : ℝ) : ℂ) := by
  rw [Matrix.adjugate_mul_distrib, ← Matrix.adjugate_conjTranspose]
  exact trace_conjTranspose_mul_self _

theorem trace_adj_mat4 (A : Mat4) :
    6 * Matrix.trace A.adjugate = Matrix.trace A ^ 3 - 3 * Matrix.trace A * Matrix.trace (A * A) +
      2 * Matrix.trace (A * A * A) := by
  have := trace_adj_fin4 (toF A)
  simp only [← toF_adjugate, ← toF_mul, toF_trace] at this
  exact this


theorem trace_gram_self (M : Mat4) :
    Matrix.trace (M * Mᴴ) = ((∑ p, ∑ q, Complex.normSq (M p q) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.star_def, mul_comm _ ((starRingEnd ℂ) _),
    ← Complex.normSq_eq_conj_mul_self]

theorem re_trace_formula (A : Mat4) (n : ℝ) (hA : Matrix.trace A = (n : ℂ)) :
    6 * (Matrix.trace A.adjugate).re =
      n ^ 3 - 3 * n * (Matrix.trace (A * A)).re + 2 * (Matrix.trace (A * A * A)).re := by
  have h := trace_adj_mat4 A
  rw [hA] at h
  have := congrArg Complex.re h
  simp [Complex.mul_re, pow_succ] at this
  linarith [this]

/-! ### Cut 12: conjugation by the magic basis -/

theorem red12_psiZ (Z : Mat4) : red12 (psiZ Z) = magicB * (Z * Zᴴ) * magicBᴴ := by
  have hU : magicBᵀ * magicB.map star = 1 := unitary_transpose_mul magicB_unitary
  rw [red12_eq, zmat_psiZ]
  calc magicB * Z * magicBᵀ * (magicB * Z * magicBᵀ)ᴴ
      = magicB * Z * (magicBᵀ * magicB.map star) * Zᴴ * magicBᴴ := by
        simp only [Matrix.conjTranspose_mul, transpose_conjTranspose, Matrix.mul_assoc]
    _ = magicB * (Z * Zᴴ) * magicBᴴ := by
        rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem trace_conjB (W : Mat4) : Matrix.trace (magicB * W * magicBᴴ) = Matrix.trace W := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, magicB_unitary, Matrix.one_mul]

theorem sq_conjB (W : Mat4) :
    (magicB * W * magicBᴴ) * (magicB * W * magicBᴴ) = magicB * (W * W) * magicBᴴ := by
  calc (magicB * W * magicBᴴ) * (magicB * W * magicBᴴ)
      = magicB * W * (magicBᴴ * magicB) * W * magicBᴴ := by simp only [Matrix.mul_assoc]
    _ = magicB * (W * W) * magicBᴴ := by rw [magicB_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem cube_conjB (W : Mat4) :
    (magicB * W * magicBᴴ) * (magicB * W * magicBᴴ) * (magicB * W * magicBᴴ) =
      magicB * (W * W * W) * magicBᴴ := by
  rw [sq_conjB]
  calc (magicB * (W * W) * magicBᴴ) * (magicB * W * magicBᴴ)
      = magicB * (W * W) * (magicBᴴ * magicB) * W * magicBᴴ := by simp only [Matrix.mul_assoc]
    _ = magicB * (W * W * W) * magicBᴴ := by rw [magicB_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-! ### The identity -/

/-- `N = Z Zᵀ Z - (tr ZᵀZ / 2) Z`. -/
def Nm (Z : Mat4) : Mat4 := Z * Zᵀ * Z - (Matrix.trace (Zᵀ * Z) / 2) • Z

theorem toF_Nm (Z : Mat4) : toF (Nm Z) = Nf (toF Z) := by
  unfold Nm Nf
  have h1 : toF (Z * Zᵀ * Z) = toF Z * (toF Z)ᵀ * toF Z := by
    rw [toF_mul, toF_mul, toF_transpose]
  have h2 : Matrix.trace (Zᵀ * Z) = Matrix.trace ((toF Z)ᵀ * toF Z) := by
    rw [← toF_trace, toF_mul, toF_transpose]
  have h3 : toF ((Matrix.trace (Zᵀ * Z) / 2) • Z) = (Matrix.trace ((toF Z)ᵀ * toF Z) / 2) • toF Z := by
    rw [h2]; rfl
  have h4 : toF (Z * Zᵀ * Z - (Matrix.trace (Zᵀ * Z) / 2) • Z) =
      toF (Z * Zᵀ * Z) - toF ((Matrix.trace (Zᵀ * Z) / 2) • Z) := rfl
  rw [h4, h1, h3]

theorem cut13_sum (Z : Mat4) :
    ∑ p, ∑ q, Complex.normSq ((cut13 (psiZ Z)).adjugate p q) =
      ∑ i, ∑ j, Complex.normSq (alpha13 (toF Z).adjugate (Nf (toF Z)) i j) := by
  have key : ∀ i j, (cut13 (psiZ Z)).adjugate (pairEquiv.symm i) (pairEquiv.symm j) =
      alpha13 (toF Z).adjugate (Nf (toF Z)) i j := by
    intro i j
    have := congrFun (congrFun (toF_adjugate (cut13 (psiZ Z))) i) j
    rw [toF_cut13, adj13_eq] at this
    exact this
  simp only [← key]
  exact (sum_toF (fun p q => Complex.normSq ((cut13 (psiZ Z)).adjugate p q))).symm

theorem cut14_sum (Z : Mat4) :
    ∑ p, ∑ q, Complex.normSq ((cut14 (psiZ Z)).adjugate p q) =
      ∑ i, ∑ j, Complex.normSq (alpha14 (toF Z).adjugate (Nf (toF Z)) i j) := by
  have key : ∀ i j, (cut14 (psiZ Z)).adjugate (pairEquiv.symm i) (pairEquiv.symm j) =
      alpha14 (toF Z).adjugate (Nf (toF Z)) i j := by
    intro i j
    have := congrFun (congrFun (toF_adjugate (cut14 (psiZ Z))) i) j
    rw [toF_cut14, adj14_eq] at this
    exact this
  simp only [← key]
  exact (sum_toF (fun p q => Complex.normSq ((cut14 (psiZ Z)).adjugate p q))).symm

/-- **`eq:fqe-global-intrinsic`**: `Q` of the state with magic matrix `Z`. -/
theorem sexticQ_psiZ (Z : Mat4) :
    sexticQ (psiZ Z) =
      -4 * (∑ p, ∑ q, Complex.normSq (Z p q)) ^ 3 +
        27 * (∑ p, ∑ q, Complex.normSq (Z p q)) * (Matrix.trace (Z * Zᴴ * (Z * Zᴴ))).re -
        18 * (Matrix.trace (Z * Zᴴ * (Z * Zᴴ) * (Z * Zᴴ))).re -
        18 * ∑ p, ∑ q, Complex.normSq (Nm Z p q) := by
  set ψ := psiZ Z with hψ
  set n := ∑ p, ∑ q, Complex.normSq (Z p q) with hn
  have hcoord : magicCoord (zmat ψ) = Z := coord_of_eq (zmat_psiZ Z)
  have hnψ : normSqPsi ψ = n := by rw [← frob_coord ψ, hcoord]
  set W := Z * Zᴴ with hW
  set Ea := ∑ p, ∑ q, Complex.normSq (Z.adjugate p q) with hEa
  set NN := ∑ p, ∑ q, Complex.normSq (Nm Z p q) with hNN
  -- the three cuts
  have e12 := re_trace_formula (red12 ψ) n (by rw [trace_red12, hnψ])
  have e13 := re_trace_formula (red13 ψ) n (by rw [trace_red13, hnψ])
  have e14 := re_trace_formula (red14 ψ) n (by rw [trace_red14, hnψ])
  have hQ := sexticQ_eq ψ
  unfold purity cubicMoment at hQ
  rw [hnψ] at hQ
  -- cut 12 equals the Gram matrix `Z Zᴴ`
  have hW1 : Matrix.trace W = (n : ℂ) := trace_gram_self Z
  have eW := re_trace_formula W n hW1
  have hEaW : (Matrix.trace W.adjugate).re = Ea := by
    rw [hW, trace_adj_gram, Complex.ofReal_re]
  have h12sq : Matrix.trace (red12 ψ * red12 ψ) = Matrix.trace (W * W) := by
    rw [red12_psiZ, sq_conjB, trace_conjB]
  have h12cu : Matrix.trace (red12 ψ * red12 ψ * red12 ψ) = Matrix.trace (W * W * W) := by
    rw [red12_psiZ, cube_conjB, trace_conjB]
  rw [h12sq, h12cu] at e12 hQ
  have hr12 : (Matrix.trace (red12 ψ).adjugate).re = Ea := by linarith [eW, hEaW]
  -- cuts 13 and 14
  have hS13 : (Matrix.trace (red13 ψ).adjugate).re =
      ∑ i, ∑ j, Complex.normSq (alpha13 (toF Z).adjugate (Nf (toF Z)) i j) := by
    rw [red13_eq, trace_adj_gram, Complex.ofReal_re]
    exact cut13_sum Z
  have hS14 : (Matrix.trace (red14 ψ).adjugate).re =
      ∑ i, ∑ j, Complex.normSq (alpha14 (toF Z).adjugate (Nf (toF Z)) i j) := by
    rw [red14_eq, trace_adj_gram, Complex.ofReal_re]
    exact cut14_sum Z
  have hquad := quad_identity (toF Z).adjugate (Nf (toF Z))
  have hEaF : ∑ i, ∑ j, Complex.normSq ((toF Z).adjugate i j) = Ea := by
    have : ∀ i j, (toF Z).adjugate i j = Z.adjugate (pairEquiv.symm i) (pairEquiv.symm j) := by
      intro i j; rw [← toF_adjugate]; rfl
    simp only [this]
    exact sum_toF (fun p q => Complex.normSq (Z.adjugate p q))
  have hNF : ∑ i, ∑ j, Complex.normSq (Nf (toF Z) i j) = NN := by
    have : ∀ i j, Nf (toF Z) i j = Nm Z (pairEquiv.symm i) (pairEquiv.symm j) := by
      intro i j; rw [← toF_Nm]; rfl
    simp only [this]
    exact sum_toF (fun p q => Complex.normSq (Nm Z p q))
  rw [hS13] at e13
  rw [hS14] at e14
  rw [hr12] at e12
  rw [hEaF, hNF] at hquad
  linarith [e12, e13, e14, hQ, hquad, eW, hEaW]

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.sexticQ_psiZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sexticQ_psiZ

end

end FormalResearch.FourQubitEntropy.GO
