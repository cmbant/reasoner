module

/-
Stormer.lean

Størmer's theorem (Acta Math. 110, 233 (1963)), formally: every positive linear map M₂(ℂ) → M₂(ℂ) is
decomposable. So the (2,2) link type is readable, the first case of the readable direction of the
alpha Letter's read cap proved without hypotheses.

The state form is Physical Superintelligence's Lean theorem `ThreeCopyQutritWerner.twoQubit_ppt_separable`
(every positive two-qubit operator with positive partial transpose is a finite sum of positive product
operators), vendored unchanged under `ThirdParty/PSI` (Apache License 2.0). `Duality.lean` turns a state
statement of this kind into the map statement. What is new here is the translation between the two
libraries' definitions and the assembly.
-/
public import MathLab.ChainTheory.Duality
public import ThreeCopyQutritWerner.TwoQubitPPTSufficiency

@[expose] public section

open Matrix ComplexOrder
open scoped Kronecker

noncomputable section

namespace ChainStormer

open ChoiDark ChainReadCap ChainDuality

variable {n m : ℕ}

/-- Our positive semidefinite predicate gives Mathlib's. -/
theorem posSemidef_of_isPSD {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (h : IsPSD P) :
    P.PosSemidef :=
  Matrix.posSemidef_iff_dotProduct_mulVec.2
    ⟨h.hermitian, fun x => Complex.nonneg_iff.2 ⟨(h x).1, (h x).2.symm⟩⟩

/-- Mathlib's positive semidefinite matrices are Gram matrices `Cᴴ C`. -/
theorem posSemidef_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (h : P.PosSemidef) :
    ∃ C : Matrix ι ι ℂ, P = Cᴴ * C := by
  open scoped MatrixOrder in
  exact CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (Matrix.nonneg_iff_posSemidef.2 h)

/-- Separability with the product vectors indexed by any finite type. -/
theorem isSeparable_of_fintype {ι : Type*} [Fintype ι] (x : ι → Fin n → ℂ) (y : ι → Fin m → ℂ) :
    IsSeparable (∑ i, vecMulVec (prodVec (x i) (y i)) (star (prodVec (x i) (y i)))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, fun s => x (e s), fun s => y (e s),
    (Equiv.sum_comp e (fun i => vecMulVec (prodVec (x i) (y i)) (star (prodVec (x i) (y i))))).symm⟩

/-- **PSI's separability gives ours**: a nonnegative combination of positive product operators
`Σ pₖ Aₖ ⊗ Bₖ` is a sum of rank-one product projectors. -/
theorem isSeparable_of_bipartite {ρ : Mat n m} (h : ThreeCopyQutritWerner.IsBipartiteSeparable ρ) :
    IsSeparable ρ := by
  classical
  obtain ⟨K, p, A, B, hp, hA, hB, rfl⟩ := h
  choose C hC using fun k => posSemidef_gram (hA k)
  choose D hD using fun k => posSemidef_gram (hB k)
  have key := isSeparable_of_fintype (ι := Fin K × Fin n × Fin m)
    (fun t => fun a => ((Real.sqrt (p t.1) : ℝ) : ℂ) * star (C t.1 t.2.1 a))
    (fun t => fun b => star (D t.1 t.2.2 b))
  convert key using 1
  ext x y
  have hs : ∀ k, ((Real.sqrt (p k) : ℝ) : ℂ) * star ((Real.sqrt (p k) : ℝ) : ℂ) = ((p k : ℝ) : ℂ) := by
    intro k
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp k)]
  simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply, hC, hD, Matrix.mul_apply,
    conjTranspose_apply, vecMulVec_apply, prodVec, Pi.star_apply, star_mul', star_star,
    Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hs k]
  ring

/-- **Every PPT operator on ℂ² ⊗ ℂ² is separable** (PSI's theorem, in this library's terms). -/
theorem pptSeparable22 : AllPPTSeparable 2 2 := fun ρ hρ =>
  isSeparable_of_bipartite
    (ThreeCopyQutritWerner.twoQubit_ppt_separable ρ (posSemidef_of_isPSD hρ.1)
      (show (ThreeCopyQutritWerner.partialTranspose ρ).PosSemidef from posSemidef_of_isPSD hρ.2))

/-- **Størmer's theorem**: every positive linear map `M₂(ℂ) → M₂(ℂ)` is decomposable. -/
theorem stormer : AllDecomposable 2 2 :=
  allDecomposable_of_allPPTSeparable pptSeparable22

/-- **The (2,2) type is readable**, with no hypothesis. -/
theorem readable_two_two : Readable 2 2 :=
  readable_iff_allDecomposable.2 stormer

end ChainStormer

end

end -- public section

#print axioms ChainStormer.isSeparable_of_bipartite
#print axioms ChainStormer.stormer
#print axioms ChainStormer.readable_two_two
