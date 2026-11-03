import FormalResearch.PPTThreeQubit.PencilKernel
import FormalResearch.PPTThreeQubit.MomentCone
import FormalResearch.PPTThreeQubit.CutEquiv

/-!
# The cut curves of a product-free five-dimensional support

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/appendix_moment_cone.tex`
(proof of `thm:ppt3-universal-moments`) and `relaxations_and_scope.tex`.

For a cut `e : Fin 8 ≃ Fin 2 × Fin 4`, a basis matrix `K` (`8 × 3`) of `R^⊥` gives the `3 × 4` pencil
`M(a) = Kᴴ (a ⊗ ·) = a₀ M₀ + a₁ M₁` (`pencil0`, `pencil1`).  Product-freeness of `R^⊥` is exactly
`RowsIndep` of `M(a)` for all `a ≠ 0` (`rowsIndep_pencil`).  The kernel of `M(a)` is spanned by the cubic
cofactor vector `b(a)` (`PencilKernel`), `a ⊗ b(a) = L ν(a)` with the `8 × 5` matrix `curveMat`, `L` has
rank five (`curveMat_injective`, from `cofCoeff_indep`), its columns lie in `R` (`conjTranspose_mul_curveMat`),
so `L = B T` with `T` invertible (`curve_cut`).  `ppt3_universal_moments` assembles the three cuts and
the two cone statements of `MomentCone`.  Everything is unconditional linear algebra; the Horodecki
hypothesis enters only in `MomentConeGME`.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

/-- The product vector `a ⊗ b` across the cut `e`. -/
def kronE (e : Fin 8 ≃ Fin 2 × Fin 4) (a : Fin 2 → ℂ) (b : Fin 4 → ℂ) : Fin 8 → ℂ :=
  fun j => a (e j).1 * b (e j).2

section Cut

variable (e : Fin 8 ≃ Fin 2 × Fin 4) (K : Matrix (Fin 8) (Fin 3) ℂ)

/-- The coefficient matrices of the pencil `M(a) = Kᴴ (a ⊗ ·)`, `M(a) = a₀ M₀ + a₁ M₁`. -/
def pencil0 : Matrix (Fin 3) (Fin 4) ℂ := Matrix.of fun r k => star (K (e.symm (0, k)) r)

def pencil1 : Matrix (Fin 3) (Fin 4) ℂ := Matrix.of fun r k => star (K (e.symm (1, k)) r)

theorem conjTranspose_mulVec_kronE (α : Fin 2 → ℂ) (μ : Fin 4 → ℂ) :
    Kᴴ *ᵥ kronE e α μ = (α 0 • pencil0 e K + α 1 • pencil1 e K) *ᵥ μ := by
  ext r
  simp only [mulVec, dotProduct, conjTranspose_apply, kronE]
  rw [← Equiv.sum_comp e.symm]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, pencil0, pencil1, Finset.sum_add_distrib,
    add_mul, mul_assoc, mul_left_comm]

theorem norm_ne_zero {a0 a1 : ℂ} (h : ¬ (a0 = 0 ∧ a1 = 0)) : a0 * star a0 + a1 * star a1 ≠ 0 := by
  have : a0 * star a0 + a1 * star a1 = ((Complex.normSq a0 + Complex.normSq a1 : ℝ) : ℂ) := by
    simp [Complex.mul_conj]
  rw [this, Ne, Complex.ofReal_eq_zero]
  intro h0
  apply h
  have h1 := Complex.normSq_nonneg a0
  have h2 := Complex.normSq_nonneg a1
  exact ⟨Complex.normSq_eq_zero.1 (by linarith), Complex.normSq_eq_zero.1 (by linarith)⟩

theorem orth_prod {a0 a1 q0 q1 : ℂ} (hn : a0 * star a0 + a1 * star a1 ≠ 0)
    (h : star a0 * q0 + star a1 * q1 = 0) :
    q0 = (-star a1) * ((-a1 * q0 + a0 * q1) / (a0 * star a0 + a1 * star a1)) ∧
    q1 = star a0 * ((-a1 * q0 + a0 * q1) / (a0 * star a0 + a1 * star a1)) := by
  constructor
  · rw [← mul_div_assoc, eq_div_iff hn]
    linear_combination a0 * h
  · rw [← mul_div_assoc, eq_div_iff hn]
    linear_combination a1 * h

/-- Constant rank three: if `R^⊥ = range K` contains no nonzero product vector across the cut `e`, then
the pencil `M(a) = Kᴴ(a ⊗ ·)` has independent rows for every `a ≠ 0`. -/
theorem rowsIndep_pencil (hfree : ∀ y : Fin 3 → ℂ, y ≠ 0 → ¬ IsProdE e (K *ᵥ y)) (a0 a1 : ℂ)
    (h : ¬ (a0 = 0 ∧ a1 = 0)) : RowsIndep (a0 • pencil0 e K + a1 • pencil1 e K) := by
  intro y hy
  by_contra hy0
  apply hfree (star y) (star_ne_zero.2 hy0)
  set q : Fin 8 → ℂ := K *ᵥ star y with hq
  have hcol : ∀ k, star a0 * q (e.symm (0, k)) + star a1 * q (e.symm (1, k)) = 0 := by
    intro k
    have := congrFun hy k
    simp only [vecMul, dotProduct, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pencil0,
      pencil1, of_apply, Pi.zero_apply] at this
    have h2 := congrArg star this
    simp only [star_sum, star_mul', star_add, star_star, star_zero] at h2
    simp only [hq, mulVec, dotProduct, Pi.star_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [← h2]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hn := norm_ne_zero h
  refine ⟨![-star a1, star a0], fun k =>
    (-a1 * q (e.symm (0, k)) + a0 * q (e.symm (1, k))) / (a0 * star a0 + a1 * star a1), fun j => ?_⟩
  rcases hp : e j with ⟨i, k⟩
  have hj : j = e.symm (i, k) := by rw [← hp]; simp
  have hc := hcol k
  obtain ⟨h0, h1⟩ := orth_prod hn hc
  rw [hj]
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- The coefficient vector in `ν`-coordinates of the `(i, k)` entry of `a ⊗ b(a)`, where
`b(a) = ∑ₘ a₀^{3-m} a₁^m βₘ`. -/
def Lp (β : Fin 4 → Fin 4 → ℂ) (i : Fin 2) (k : Fin 4) : Fin 5 → ℂ :=
  if i = 0 then ![β 0 k, β 1 k, β 2 k, β 3 k, 0] else ![0, β 0 k, β 1 k, β 2 k, β 3 k]

theorem Lp_dot_nu (β : Fin 4 → Fin 4 → ℂ) (i : Fin 2) (k : Fin 4) (a : Fin 2 → ℂ) :
    Lp β i k ⬝ᵥ nuVec a = a i * ∑ n : Fin 4, (a 0 ^ (3 - (n : ℕ)) * a 1 ^ (n : ℕ)) * β n k := by
  fin_cases i
  · simp [Lp, nuVec, dotProduct, Fin.sum_univ_five, Fin.sum_univ_four]
    ring
  · simp [Lp, nuVec, dotProduct, Fin.sum_univ_five, Fin.sum_univ_four]
    ring

/-- The `8 × 5` matrix `L` with `a ⊗ b(a) = L ν(a)`. -/
def curveMat : Matrix (Fin 8) (Fin 5) ℂ :=
  Matrix.of fun j => Lp (cofCoeff (pencil0 e K) (pencil1 e K)) (e j).1 (e j).2

theorem curveMat_mulVec_nu (a : Fin 2 → ℂ) :
    curveMat e K *ᵥ nuVec a = kronE e a (cof3 (a 0 • pencil0 e K + a 1 • pencil1 e K)) := by
  ext j
  simp only [mulVec, curveMat, of_apply, Lp_dot_nu, kronE]
  rw [cof3_pencil]
  simp [Finset.sum_apply]

theorem poly5_zero (c : Fin 5 → ℂ) (h : ∀ t : ℂ, ∑ m : Fin 5, c m * t ^ (m : ℕ) = 0) : c = 0 := by
  have hp : (∑ m : Fin 5, Polynomial.C (c m) * Polynomial.X ^ (m : ℕ)) = 0 := by
    apply Polynomial.funext
    intro t
    simp [Polynomial.eval_finsetSum, h t]
  ext m
  have := congrArg (fun p => p.coeff (m : ℕ)) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using this

theorem nuVec_one (t : ℂ) : nuVec ![1, t] = fun m : Fin 5 => t ^ (m : ℕ) := by
  ext m; fin_cases m <;> simp [nuVec]

/-- The columns of `L` lie in `R = ker Kᴴ`: `Kᴴ L = 0` (coefficients of the zero polynomial). -/
theorem conjTranspose_mul_curveMat : Kᴴ * curveMat e K = 0 := by
  ext r m
  have hr : ∀ t : ℂ, ∑ m : Fin 5, (Kᴴ * curveMat e K) r m * t ^ (m : ℕ) = 0 := by
    intro t
    have h1 : (Kᴴ * curveMat e K) *ᵥ nuVec ![1, t] = 0 := by
      rw [← mulVec_mulVec, curveMat_mulVec_nu, conjTranspose_mulVec_kronE]
      exact mulVec_cof3 _
    have := congrFun h1 r
    rw [nuVec_one] at this
    simpa [mulVec, dotProduct] using this
  have := poly5_zero (fun m => (Kᴴ * curveMat e K) r m) hr
  exact congrFun this m

/-- The four coefficient vectors `βₘ` as the rows of a `4 × 4` matrix. -/
def betaMat : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun m k => cofCoeff (pencil0 e K) (pencil1 e K) m k

theorem isUnit_betaMat (hfree : ∀ y : Fin 3 → ℂ, y ≠ 0 → ¬ IsProdE e (K *ᵥ y)) :
    IsUnit (betaMat e K) := by
  rw [← mulVec_injective_iff_isUnit]
  rw [← coe_mulVecLin, injective_iff_map_eq_zero]
  intro lam hlam
  simp only [coe_mulVecLin] at hlam
  refine cofCoeff_indep _ _ (fun a0 a1 h => rowsIndep_pencil e K hfree a0 a1 h) lam fun m => ?_
  have := congrFun hlam m
  simpa [betaMat, mulVec, dotProduct, mul_comm] using this

theorem curveMat_injective (hfree : ∀ y : Fin 3 → ℂ, y ≠ 0 → ¬ IsProdE e (K *ᵥ y)) :
    Function.Injective (curveMat e K).mulVec := by
  rw [← coe_mulVecLin, injective_iff_map_eq_zero]
  intro c hc
  simp only [coe_mulVecLin] at hc
  have hT : Function.Injective (betaMat e K)ᵀ.mulVec := by
    rw [mulVec_injective_iff_isUnit, isUnit_transpose]; exact isUnit_betaMat e K hfree
  rw [← coe_mulVecLin, injective_iff_map_eq_zero] at hT
  simp only [coe_mulVecLin] at hT
  have e0 : (betaMat e K)ᵀ *ᵥ (fun n : Fin 4 => c n.castSucc) = 0 := by
    ext k
    have := congrFun hc (e.symm (0, k))
    simp [curveMat, mulVec, Lp, dotProduct, Fin.sum_univ_five, Fin.sum_univ_four, betaMat,
      transpose_apply] at this ⊢
    linear_combination this
  have e1 : (betaMat e K)ᵀ *ᵥ (fun n : Fin 4 => c n.succ) = 0 := by
    ext k
    have := congrFun hc (e.symm (1, k))
    simp [curveMat, mulVec, Lp, dotProduct, Fin.sum_univ_five, Fin.sum_univ_four, betaMat,
      transpose_apply] at this ⊢
    linear_combination this
  have h0 := hT _ e0
  have h1 := hT _ e1
  ext m
  fin_cases m
  · exact congrFun h0 0
  · exact congrFun h0 1
  · exact congrFun h0 2
  · exact congrFun h0 3
  · exact congrFun h1 3

end Cut

/-- `R = ker Kᴴ`: if `B` (`8 × 5`) and `K` (`8 × 3`) have full column rank and `Kᴴ B = 0`, every vector
annihilated by `Kᴴ` lies in `range B` (dimension count `5 + 3 = 8`). -/
theorem exists_eq_mulVec_of_conjTranspose_mulVec_eq_zero (B : Matrix (Fin 8) (Fin 5) ℂ)
    (K : Matrix (Fin 8) (Fin 3) ℂ) (hB : Function.Injective B.mulVec)
    (hK : Function.Injective K.mulVec) (hKB : Kᴴ * B = 0) (x : Fin 8 → ℂ) (hx : Kᴴ *ᵥ x = 0) :
    ∃ y, x = B *ᵥ y := by
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker Kᴴ.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    simp only [LinearMap.mem_ker, coe_mulVecLin, mulVec_mulVec, hKB, zero_mulVec]
  have h1 : Module.finrank ℂ (LinearMap.range B.mulVecLin) = 5 := by
    rw [LinearMap.finrank_range_of_inj hB]; simp
  have h2 : Module.finrank ℂ (LinearMap.range Kᴴ.mulVecLin) = 3 := by
    have : Kᴴ.rank = K.rank := rank_conjTranspose K
    have h3 : K.rank = 3 := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj hK]; simp
    exact this.trans h3
  have h4 := LinearMap.finrank_range_add_finrank_ker Kᴴ.mulVecLin
  simp only [Module.finrank_fin_fun] at h4
  have h5 : Module.finrank ℂ (LinearMap.ker Kᴴ.mulVecLin) = 5 := by omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h5])
  have hx' : x ∈ LinearMap.ker Kᴴ.mulVecLin := by simpa using hx
  rw [← heq] at hx'
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy.symm⟩

theorem kronE_smul (e : Fin 8 ≃ Fin 2 × Fin 4) (a : Fin 2 → ℂ) (b : Fin 4 → ℂ) (s : ℂ) :
    kronE e a (s • b) = s • kronE e a b := by
  ext j; simp [kronE]; ring

/-- **The curve part of `thm:ppt3-universal-moments` for one cut.**  Let `B` (`8 × 5`) and `K` (`8 × 3`)
have full column rank with `Kᴴ B = 0` (so `K` is a basis matrix of `R^⊥`, `R = range B`), and suppose
`range K` contains no nonzero product vector across the cut `e`.  Then there is an invertible `T` such
that the cut-`e` product vectors of `R` are exactly the multiples of `B T ν(a)`, `a ≠ 0`.
Proved without the Kronecker canonical form (`cofCoeff_indep`). -/
theorem curve_cut (B : Matrix (Fin 8) (Fin 5) ℂ) (K : Matrix (Fin 8) (Fin 3) ℂ)
    (hB : Function.Injective B.mulVec) (hKB : Kᴴ * B = 0) (e : Fin 8 ≃ Fin 2 × Fin 4)
    (hfree : ∀ y : Fin 3 → ℂ, y ≠ 0 → ¬ IsProdE e (K *ᵥ y)) :
    ∃ T : Matrix (Fin 5) (Fin 5) ℂ, IsUnit T.det ∧ ∀ y : Fin 5 → ℂ, IsProdE e (B *ᵥ y) ↔
      ∃ (a : Fin 2 → ℂ) (s : ℂ), a ≠ 0 ∧ B *ᵥ y = s • (B *ᵥ (T *ᵥ nuVec a)) := by
  have hK : Function.Injective K.mulVec := by
    rw [← coe_mulVecLin, injective_iff_map_eq_zero]
    intro y hy
    simp only [coe_mulVecLin] at hy
    by_contra hy0
    exact hfree y hy0 ⟨0, 0, fun i => by simp [hy]⟩
  have hcol : ∀ m : Fin 5, ∃ u : Fin 5 → ℂ, (fun j => curveMat e K j m) = B *ᵥ u := by
    intro m
    refine exists_eq_mulVec_of_conjTranspose_mulVec_eq_zero B K hB hK hKB _ ?_
    ext r
    have := congrFun (congrFun (conjTranspose_mul_curveMat e K) r) m
    simpa [mulVec, dotProduct, Matrix.mul_apply] using this
  choose u hu using hcol
  set T : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun k m => u m k with hT
  have hBT : B * T = curveMat e K := by
    ext j m
    have := congrFun (hu m) j
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, hT, of_apply]
    exact this.symm
  have hTL : ∀ a, B *ᵥ (T *ᵥ nuVec a) = kronE e a (cof3 (a 0 • pencil0 e K + a 1 • pencil1 e K)) := by
    intro a
    rw [mulVec_mulVec, hBT, curveMat_mulVec_nu]
  refine ⟨T, ?_, ?_⟩
  · rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit, ← coe_mulVecLin,
      injective_iff_map_eq_zero]
    intro c hc
    simp only [coe_mulVecLin] at hc
    have : curveMat e K *ᵥ c = 0 := by rw [← hBT, ← mulVec_mulVec, hc, mulVec_zero]
    exact curveMat_injective e K hfree (by simpa using this)
  · intro y
    constructor
    · rintro ⟨α, μ, hαμ⟩
      have hBy : B *ᵥ y = kronE e α μ := funext hαμ
      by_cases h0 : B *ᵥ y = 0
      · refine ⟨![1, 0], 0, ?_, by rw [h0, zero_smul]⟩
        intro h
        have := congrFun h 0
        simp at this
      · have hα : ¬ (α 0 = 0 ∧ α 1 = 0) := by
          rintro ⟨h0', h1'⟩
          apply h0
          have : α = 0 := by ext i; fin_cases i <;> simp [h0', h1']
          rw [hBy, this]
          ext j; simp [kronE]
        have hker : (α 0 • pencil0 e K + α 1 • pencil1 e K) *ᵥ μ = 0 := by
          rw [← conjTranspose_mulVec_kronE, ← hBy, mulVec_mulVec, hKB, zero_mulVec]
        obtain ⟨c, hc⟩ := exists_smul_cof3_of_mulVec_eq_zero (rowsIndep_pencil e K hfree _ _ hα) μ hker
        refine ⟨α, c, fun h => hα (by simp [h]), ?_⟩
        rw [hTL, hBy, hc, kronE_smul]
    · rintro ⟨a, s, ha, h⟩
      rw [h, hTL]
      exact ⟨s • a, cof3 (a 0 • pencil0 e K + a 1 • pencil1 e K), fun j => by simp [kronE]; ring⟩

/-- The reindexing of cut `c ∈ {A, B, C}`. -/
def cutEquiv : Fin 3 → (Fin 8 ≃ Fin 2 × Fin 4)
  | 0 => eqA
  | 1 => eqB
  | 2 => eqC

theorem isCutProdAt_iff (c : Fin 3) (x : Fin 8 → ℂ) : IsCutProdAt c x ↔ IsProdE (cutEquiv c) x := by
  fin_cases c <;> exact Iff.rfl

/-- **`thm:ppt3-universal-moments`** (source `relaxations_and_scope.tex`, proof in
`appendix_moment_cone.tex`), proved from its hypotheses without the Kronecker canonical form.

Let `B` (`8 × 5`) be a basis matrix of a subspace `R` and `K` (`8 × 3`) a basis matrix of `R^⊥`
(`B`, `K` of full column rank, `Kᴴ B = 0`), and suppose `R^⊥` contains no nonzero vector that is a
product across any of the three cuts.  Then there are invertible `T_c` (`c = A, B, C`) such that

* the cut-`c` product vectors of `R` are exactly the multiples of `B T_c ν(a)`, `a ≠ 0` (`CutCurve`);
* `B X Bᴴ` is biseparable iff `X ∈ ∑_c T_c 𝓜₄ T_cᴴ` (`eq:ppt3-universal-bs`);
* `Re tr(H X) ≥ 0` for all biseparable `B X Bᴴ` iff `Re ν(a)ᴴ T_cᴴ H T_c ν(a) ≥ 0` for all `a`, `c`
  (`eq:ppt3-universal-dual`).

No hypothesis beyond those stated; in particular nothing from the Horodecki 2⊗3 theorem is used here.
Not formalised: the Carathéodory bound "at most 25 cut-product projectors" and closedness of the cone;
`H`, `X` are not required to be Hermitian (the statements hold without). -/
theorem ppt3_universal_moments (B : Matrix (Fin 8) (Fin 5) ℂ) (K : Matrix (Fin 8) (Fin 3) ℂ)
    (hB : Function.Injective B.mulVec) (hKB : Kᴴ * B = 0)
    (hfree : ∀ y : Fin 3 → ℂ, y ≠ 0 → ¬ IsCutProduct (K *ᵥ y)) :
    ∃ T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ, (∀ c, IsUnit (T c).det) ∧ CutCurve B T ∧
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) ↔ InMomentCone T X) ∧
      (∀ H : Matrix (Fin 5) (Fin 5) ℂ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) → 0 ≤ (trace (H * X)).re) ↔
          ∀ (c : Fin 3) (a : Fin 2 → ℂ),
            0 ≤ (star (nuVec a) ⬝ᵥ ((T c)ᴴ * H * T c) *ᵥ nuVec a).re) := by
  have hc : ∀ c : Fin 3, ∃ T : Matrix (Fin 5) (Fin 5) ℂ, IsUnit T.det ∧
      ∀ y : Fin 5 → ℂ, IsProdE (cutEquiv c) (B *ᵥ y) ↔
        ∃ (a : Fin 2 → ℂ) (s : ℂ), a ≠ 0 ∧ B *ᵥ y = s • (B *ᵥ (T *ᵥ nuVec a)) := by
    intro c
    refine curve_cut B K hB hKB (cutEquiv c) fun y hy hp => hfree y hy ?_
    rw [isCutProduct_iff]
    exact ⟨c, (isCutProdAt_iff c _).2 hp⟩
  choose T hTu hTi using hc
  have hcurve : CutCurve B T := fun c y => by rw [isCutProdAt_iff]; exact hTi c y
  exact ⟨T, hTu, hcurve, fun X => biseparable_iff_mem_cone B T hB hcurve X,
    fun H => dual_iff B T hB hcurve H⟩

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.curve_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.curve_cut

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_universal_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.ppt3_universal_moments
