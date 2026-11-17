module

public import Mathlib
public import FormalResearch.Special.TraceFunctional

/-!
# Spectrum of the block form `C₀ = D + C'` (the "block form" step of `thm:tracecore`)

Source: `Weyl/free_fermion/paper/parts/constants.tex`, proof of `thm:tracecore`.  For a Hermitian `C` on a finite index
set `ι`, a family `U : Matrix ι s ℂ` of orthonormal vectors (`Uᴴ U = 1`; the paper's `u_r`), `Π = U Uᴴ`,
`Π' = 1 - Π`, `λ_x = Re (Uᴴ C U)_{xx} = ⟨u_x, C u_x⟩`, `D = ∑ λ_x u_x u_x*` and `C' = Π' C Π'`:

* `traceFn_block` : for every `f : ℝ → ℂ` with `f 0 = 0`,
  `Tr f(D + C') = ∑_x f(λ_x) + Tr f(C')`   (the eigenvalues of `D + C'` are the `λ_x` and those of the
  compression of `C` to `Ran Π'`; `C'` itself carries `dim Ran Π` extra zeros, which `f 0 = 0` ignores);
* `block_unit` : if `0 ≤ C ≤ 1` then `λ_x ∈ [0,1]` and the spectra of `C'` and `D + C'` lie in `[0,1]`.

The proof uses no eigenvalue bookkeeping: for a Hermitian `A` and a polynomial `p` interpolating `f` on the spectrum,
`Tr f(A) = tr p(A)` (`trace_aeval_eq`, from the spectral theorem), and `D C' = C' D = 0` gives
`p(D + C') = p(D) + p(C')` when `p(0) = 0`, with `p(D) = U p(Λ) Uᴴ`.
-/

@[expose] public section

namespace FormalResearch.Special.TraceCore

open Matrix Polynomial FormalResearch.MatrixAnalysis
open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aeval_diagonal' {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) (p : ℂ[X]) :
    aeval (diagonal d) p = diagonal (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, diagonal_add]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, diagonal_pow, Polynomial.eval_monomial]
    ext i j
    by_cases h : i = j
    · subst h; simp [algebraMap_eq_diagonal]
    · simp [h, algebraMap_eq_diagonal]

/-- `tr p(A) = ∑ᵢ p(λᵢ)` for Hermitian `A` and a complex polynomial `p`. -/
theorem trace_aeval_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (p : ℂ[X]) :
    (aeval A p).trace = ∑ i, p.eval ((hA.eigenvalues i : ℝ) : ℂ) := by
  have h := hA.spectral_theorem
  set U := hA.eigenvectorUnitary
  have h1 : aeval A p = Unitary.conjStarAlgAut ℂ _ U
      (aeval (diagonal (RCLike.ofReal ∘ hA.eigenvalues : ι → ℂ)) p) := by
    conv_lhs => rw [h]
    exact (Polynomial.aeval_algHom_apply (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) _ p)
  rw [h1, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc]
  simp [aeval_diagonal', Matrix.trace_diagonal]

/-- A polynomial agreeing with `f` on a finite set of reals. -/
lemma exists_poly_interp (f : ℝ → ℂ) (T : Finset ℝ) :
    ∃ p : ℂ[X], ∀ x ∈ T, p.eval (x : ℂ) = f x := by
  classical
  set s : Finset ℂ := T.image (fun x : ℝ => (x : ℂ)) with hs
  refine ⟨Lagrange.interpolate s (fun z : ℂ => z) (fun z => f z.re), fun x hx => ?_⟩
  have hxs : (x : ℂ) ∈ s := Finset.mem_image.2 ⟨x, hx, rfl⟩
  have := Lagrange.eval_interpolate_at_node (r := fun z : ℂ => f z.re) (v := fun z : ℂ => z)
    (Set.injOn_id (s : Set ℂ)) hxs
  exact this

lemma traceFn_eq_trace_aeval {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) (p : ℂ[X])
    (hp : ∀ i, p.eval ((hA.eigenvalues i : ℝ) : ℂ) = f (hA.eigenvalues i)) :
    traceFn f hA = (aeval A p).trace := by
  rw [trace_aeval_eq hA p]
  unfold traceFn
  exact Finset.sum_congr rfl fun i _ => (hp i).symm

section Block

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The projection `Π' = 1 - U Uᴴ`. -/
noncomputable def projC (U : Matrix ι s ℂ) : Matrix ι ι ℂ := 1 - U * Uᴴ

/-- `D = U diag(λ) Uᴴ`. -/
noncomputable def blockD (U : Matrix ι s ℂ) (lam : s → ℝ) : Matrix ι ι ℂ :=
  U * diagonal (fun x => (lam x : ℂ)) * Uᴴ

/-- `C' = Π' C Π'`. -/
noncomputable def blockC' (U : Matrix ι s ℂ) (C : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  projC U * C * projC U

variable {U : Matrix ι s ℂ}

omit [Fintype ι] [DecidableEq s] in
lemma projC_conjTranspose (U : Matrix ι s ℂ) : (projC U)ᴴ = projC U := by
  unfold projC
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]

lemma projC_mul_self (hU : Uᴴ * U = 1) : projC U * projC U = projC U := by
  unfold projC
  have : U * Uᴴ * (U * Uᴴ) = U * Uᴴ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU]; simp
  have h2 : (1 - U * Uᴴ) * (1 - U * Uᴴ) = 1 - U * Uᴴ - U * Uᴴ + U * Uᴴ * (U * Uᴴ) := by
    noncomm_ring
  rw [h2, this]; abel

lemma blockD_mul_C' (hU : Uᴴ * U = 1) (lam : s → ℝ) (C : Matrix ι ι ℂ) :
    blockD U lam * blockC' U C = 0 := by
  unfold blockD blockC' projC
  have h : Uᴴ * (1 - U * Uᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]
  calc U * diagonal (fun x => (lam x : ℂ)) * Uᴴ * ((1 - U * Uᴴ) * C * (1 - U * Uᴴ))
      = U * diagonal (fun x => (lam x : ℂ)) * (Uᴴ * (1 - U * Uᴴ)) * C * (1 - U * Uᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h]; simp

lemma blockC'_mul_D (hU : Uᴴ * U = 1) (lam : s → ℝ) (C : Matrix ι ι ℂ) :
    blockC' U C * blockD U lam = 0 := by
  unfold blockD blockC' projC
  have h : (1 - U * Uᴴ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  calc (1 - U * Uᴴ) * C * (1 - U * Uᴴ) * (U * diagonal (fun x => (lam x : ℂ)) * Uᴴ)
      = (1 - U * Uᴴ) * C * ((1 - U * Uᴴ) * U) * diagonal (fun x => (lam x : ℂ)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h]; simp

omit [Fintype ι] [DecidableEq ι] in
lemma blockD_isHermitian (U : Matrix ι s ℂ) (lam : s → ℝ) : (blockD U lam).IsHermitian := by
  unfold blockD
  rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    diagonal_conjTranspose]
  have : star (fun x => (lam x : ℂ)) = fun x => (lam x : ℂ) := by
    ext x; simp
  rw [this, Matrix.mul_assoc]

omit [DecidableEq s] in
lemma blockC'_isHermitian {C : Matrix ι ι ℂ} (hC : C.IsHermitian) (U : Matrix ι s ℂ) :
    (blockC' U C).IsHermitian := by
  unfold blockC'
  rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul, projC_conjTranspose, hC.eq,
    Matrix.mul_assoc]

/-- Powers of `D`. -/
lemma blockD_pow (hU : Uᴴ * U = 1) (lam : s → ℝ) (k : ℕ) :
    blockD U lam ^ (k + 1) = U * diagonal (fun x => (lam x : ℂ) ^ (k + 1)) * Uᴴ := by
  induction k with
  | zero => simp [blockD]
  | succ k ih =>
    rw [pow_succ, ih]
    unfold blockD
    have : U * diagonal (fun x => (lam x : ℂ) ^ (k + 1)) * Uᴴ * (U * diagonal (fun x => (lam x : ℂ)) * Uᴴ) =
        U * (diagonal (fun x => (lam x : ℂ) ^ (k + 1)) * (Uᴴ * U) * diagonal (fun x => (lam x : ℂ))) * Uᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hU, Matrix.mul_one, diagonal_mul_diagonal]
    simp [pow_succ]

/-- `q(D) = q(0)(1 - Π) + U q(Λ) Uᴴ`. -/
lemma aeval_blockD (hU : Uᴴ * U = 1) (lam : s → ℝ) (q : ℂ[X]) :
    aeval (blockD U lam) q = q.eval 0 • projC U +
      U * diagonal (fun x => q.eval (lam x : ℂ)) * Uᴴ := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq]
    have e1 : (p + q).eval 0 = p.eval 0 + q.eval 0 := Polynomial.eval_add
    have e2 : (diagonal fun x : s => (p + q).eval (lam x : ℂ)) =
        diagonal (fun x : s => p.eval (lam x : ℂ)) + diagonal (fun x : s => q.eval (lam x : ℂ)) := by
      rw [diagonal_add]; congr 1; ext x; exact Polynomial.eval_add
    rw [e1, e2, Matrix.mul_add, Matrix.add_mul, add_smul]; abel
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one]
    rcases k with _ | k
    · have hd : (diagonal fun x : s => Polynomial.eval (lam x : ℂ) (monomial 0 a)) = a • (1 : Matrix s s ℂ) := by
        ext i j; by_cases h : i = j <;> simp [h]
      rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, projC]
      simp only [pow_zero, mul_one]
      rw [Matrix.smul_mul, ← smul_add, sub_add_cancel]
    · have h0 : (0 : ℂ) ^ (k + 1) = 0 := by simp
      have hd : (diagonal fun x : s => Polynomial.eval (lam x : ℂ) (monomial (k + 1) a)) =
          a • diagonal (fun x : s => (lam x : ℂ) ^ (k + 1)) := by
        ext i j; by_cases h : i = j <;> simp [h]
      rw [h0, mul_zero, zero_smul, zero_add, hd, Matrix.mul_smul, Matrix.smul_mul, blockD_pow hU,
        Matrix.smul_mul]
      simp

/-- `(A + B)^(k+1) = A^(k+1) + B^(k+1)` when `AB = BA = 0`. -/
lemma add_pow_succ_of_mul_eq_zero {A B : Matrix ι ι ℂ} (hAB : A * B = 0) (hBA : B * A = 0) (k : ℕ) :
    (A + B) ^ (k + 1) = A ^ (k + 1) + B ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : A ^ (k + 1) * B = 0 := by
      rw [pow_succ, Matrix.mul_assoc, hAB, Matrix.mul_zero]
    have h2 : B ^ (k + 1) * A = 0 := by
      rw [pow_succ, Matrix.mul_assoc, hBA, Matrix.mul_zero]
    rw [pow_succ, ih, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, pow_succ A (k + 1),
      pow_succ B (k + 1)]
    simp

/-- `q(A + B) = q(A) + q(B) - q(0)` when `AB = BA = 0`. -/
lemma aeval_add_of_mul_eq_zero {A B : Matrix ι ι ℂ} (hAB : A * B = 0) (hBA : B * A = 0) (q : ℂ[X]) :
    aeval (A + B) q = aeval A q + aeval B q - q.eval 0 • (1 : Matrix ι ι ℂ) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, Polynomial.eval_add, add_smul]; abel
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one]
    rcases k with _ | k
    · simp
    · rw [add_pow_succ_of_mul_eq_zero hAB hBA]
      simp

lemma trace_blockD_aeval (hU : Uᴴ * U = 1) (lam : s → ℝ) (q : ℂ[X]) :
    (aeval (blockD U lam) q).trace =
      q.eval 0 * ((Fintype.card ι : ℂ) - Fintype.card s) + ∑ x, q.eval (lam x : ℂ) := by
  rw [aeval_blockD hU lam q, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.trace_diagonal]
  have : (projC U).trace = (Fintype.card ι : ℂ) - Fintype.card s := by
    rw [projC, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_mul_comm, hU, Matrix.trace_one]
  rw [this]; simp

/-- **Spectrum of the block form**: for `f 0 = 0`, `Tr f(D + C') = ∑_x f(λ_x) + Tr f(C')`. -/
theorem traceFn_block {C : Matrix ι ι ℂ} (hC : C.IsHermitian) (hU : Uᴴ * U = 1) (lam : s → ℝ)
    (f : ℝ → ℂ) (hf0 : f 0 = 0) :
    traceFn f ((blockD_isHermitian U lam).add (blockC'_isHermitian hC U)) =
      ∑ x, f (lam x) + traceFn f (blockC'_isHermitian hC U) := by
  classical
  set hA := (blockD_isHermitian U lam).add (blockC'_isHermitian hC U) with hAdef
  set hB := blockC'_isHermitian hC U with hBdef
  obtain ⟨p, hp⟩ := exists_poly_interp f
    ((Finset.univ.image hA.eigenvalues) ∪ (Finset.univ.image hB.eigenvalues) ∪
      (Finset.univ.image lam) ∪ {0})
  have hp0 : p.eval 0 = 0 := by
    have := hp 0 (by simp)
    simpa [hf0] using this
  have hpA : ∀ i, p.eval ((hA.eigenvalues i : ℝ) : ℂ) = f (hA.eigenvalues i) := fun i =>
    hp _ (by simp)
  have hpB : ∀ i, p.eval ((hB.eigenvalues i : ℝ) : ℂ) = f (hB.eigenvalues i) := fun i =>
    hp _ (by simp)
  have hpl : ∀ x, p.eval ((lam x : ℝ) : ℂ) = f (lam x) := fun x => hp _ (by simp)
  rw [traceFn_eq_trace_aeval hA f p hpA, traceFn_eq_trace_aeval hB f p hpB]
  have hDC := blockD_mul_C' hU lam C
  have hCD := blockC'_mul_D hU lam C
  rw [aeval_add_of_mul_eq_zero hDC hCD p, hp0, zero_smul, sub_zero, Matrix.trace_add,
    trace_blockD_aeval hU lam p, hp0, zero_mul, zero_add]
  simp only [hpl]

end Block

section Unit

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- `λ_x = Re ⟨u_x, C u_x⟩`. -/
noncomputable def blockLam (U : Matrix ι s ℂ) (C : Matrix ι ι ℂ) (x : s) : ℝ := ((Uᴴ * C * U) x x).re

lemma blockLam_mem {C : Matrix ι ι ℂ} {U : Matrix ι s ℂ} (hU : Uᴴ * U = 1) (h0 : C.PosSemidef)
    (h1 : (1 - C).PosSemidef) (x : s) : 0 ≤ blockLam U C x ∧ blockLam U C x ≤ 1 := by
  have hP := (h0.conjTranspose_mul_mul_same U).diag_nonneg (i := x)
  have hQ := ((h1.conjTranspose_mul_mul_same U).diag_nonneg (i := x))
  have e : Uᴴ * (1 - C) * U = 1 - Uᴴ * C * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
  rw [e] at hQ
  rw [Complex.nonneg_iff] at hP hQ
  refine ⟨hP.1, ?_⟩
  have := hQ.1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at this
  unfold blockLam; linarith

omit [DecidableEq s] in
lemma blockC'_psd {C : Matrix ι ι ℂ} (U : Matrix ι s ℂ) (h0 : C.PosSemidef) :
    (blockC' U C).PosSemidef := by
  have := h0.conjTranspose_mul_mul_same (projC U)
  rwa [projC_conjTranspose] at this

lemma one_sub_blockC'_psd {C : Matrix ι ι ℂ} {U : Matrix ι s ℂ} (hU : Uᴴ * U = 1)
    (h1 : (1 - C).PosSemidef) : (1 - blockC' U C).PosSemidef := by
  have hP2 := projC_mul_self hU
  have h2 := h1.conjTranspose_mul_mul_same (projC U)
  rw [projC_conjTranspose] at h2
  have hP : (U * Uᴴ).PosSemidef := by
    simpa using (posSemidef_self_mul_conjTranspose U)
  have e : 1 - blockC' U C = U * Uᴴ + projC U * (1 - C) * projC U := by
    have : projC U * (1 - C) * projC U = projC U - projC U * C * projC U := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hP2]
    rw [this, blockC']
    unfold projC; noncomm_ring
  rw [e]; exact hP.add h2

omit [DecidableEq ι] in
lemma blockD_psd {U : Matrix ι s ℂ} (lam : s → ℝ) (hl : ∀ x, 0 ≤ lam x) :
    (blockD U lam).PosSemidef := by
  have hd : (diagonal fun x => (lam x : ℂ)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro x; exact_mod_cast hl x
  exact hd.mul_mul_conjTranspose_same U

lemma one_sub_block_psd {C : Matrix ι ι ℂ} {U : Matrix ι s ℂ} (hU : Uᴴ * U = 1) (lam : s → ℝ)
    (hl : ∀ x, lam x ≤ 1) (h1 : (1 - C).PosSemidef) :
    (1 - (blockD U lam + blockC' U C)).PosSemidef := by
  have hP2 := projC_mul_self hU
  have h2 := h1.conjTranspose_mul_mul_same (projC U)
  rw [projC_conjTranspose] at h2
  have hd : (diagonal fun x => ((1 - lam x : ℝ) : ℂ)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro x; exact_mod_cast sub_nonneg.2 (hl x)
  have h3 := hd.mul_mul_conjTranspose_same U
  have e : 1 - (blockD U lam + blockC' U C) =
      U * diagonal (fun x => ((1 - lam x : ℝ) : ℂ)) * Uᴴ + projC U * (1 - C) * projC U := by
    have e1 : (diagonal fun x => ((1 - lam x : ℝ) : ℂ)) = 1 - diagonal (fun x => (lam x : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Matrix.one_apply_ne h]
    have : projC U * (1 - C) * projC U = projC U - projC U * C * projC U := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hP2]
    rw [e1, this, blockC', blockD, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    unfold projC; noncomm_ring
  rw [e]; exact h3.add h2

end Unit

/-- Hermitian `A` with `0 ≤ A ≤ 1` has all eigenvalues in `[0,1]`. -/
lemma eigenvalues_mem_unit {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h0 : A.PosSemidef)
    (h1 : (1 - A).PosSemidef) (i : ι) : hA.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨h0.eigenvalues_nonneg i, ?_⟩
  set v := hA.eigenvectorBasis i with hv
  have hnorm : star (⇑v) ⬝ᵥ ⇑v = 1 := by
    have h1 := hA.eigenvectorBasis.orthonormal.1 i
    have h2 := EuclideanSpace.inner_eq_star_dotProduct v v
    rw [dotProduct_comm] at h2
    rw [← h2, inner_self_eq_norm_sq_to_K]
    simp [hv, h1]
  have h2 := h1.re_dotProduct_nonneg (⇑v)
  have e : star (⇑v) ⬝ᵥ (1 - A) *ᵥ ⇑v = star (⇑v) ⬝ᵥ ⇑v - star (⇑v) ⬝ᵥ A *ᵥ ⇑v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  rw [e, hnorm] at h2
  have h3 := hA.eigenvalues_eq i
  simp only [RCLike.re_to_complex] at h3 h2
  rw [Complex.sub_re, Complex.one_re] at h2
  have h4 : (star (⇑v) ⬝ᵥ A *ᵥ ⇑v).re = hA.eigenvalues i := by rw [h3]
  linarith


/-- info: 'FormalResearch.Special.TraceCore.traceFn_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms traceFn_block

end FormalResearch.Special.TraceCore
