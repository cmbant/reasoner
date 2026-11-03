module

public import FormalResearch.GurvitsBarnum.Basic

/-!
# The product-kernel lemma (`lem:ppt3-product-kernel`)

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/appendix_moment_cone.tex`,
`lem:ppt3-product-kernel`.

**Hypothesis.**  The proof reduces a PPT operator on `ℂ² ⊗ ℂ⁴` with a product vector in its kernel to
a PPT operator on `ℂ² ⊗ ℂ³`, and then uses that PPT operators on `ℂ² ⊗ ℂ³` are separable
[Horodecki–Horodecki–Horodecki 1996].  Mathlib has no such theorem, so the lemma is stated with an explicit hypothesis
`PPTSeparable23`, which is discharged in `PPTSeparable23.lean` by the vendored math-lab proof
(`ThirdParty/math-lab/NOTICE.md`); the hypothesis-free statement is `ppt_product_kernel'`.  Nothing else
is assumed.

Contents.  `ptFirst` is the partial transpose on the first factor of a bipartite matrix over `ι × κ`;
`ptFirst_congr` is its compatibility with local congruences; `posSemidef_sub_schur` is the rank-one
Schur-complement subtraction; `ppt_product_kernel` is the lemma, for an arbitrary nonzero product vector
`a ⊗ b` in the kernel (the paper's local-unitary normalisation is replaced by local invertible
congruences, which preserve both separability and PPT-ness).
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.GurvitsBarnum
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The partial transpose on the first tensor factor: `(ρ^{T_1})_{(i,k),(j,l)} = ρ_{(j,k),(i,l)}`. -/
def ptFirst (ρ : Matrix (ι × κ) (ι × κ) ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.of fun p q => ρ (q.1, p.2) (p.1, q.2)

theorem ptFirst_apply (ρ : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) (k l : κ) :
    ptFirst ρ (i, k) (j, l) = ρ (j, k) (i, l) := rfl

theorem ptFirst_ptFirst (ρ : Matrix (ι × κ) (ι × κ) ℂ) : ptFirst (ptFirst ρ) = ρ := by
  ext ⟨i, k⟩ ⟨j, l⟩; rfl

theorem ptFirst_add (ρ σ : Matrix (ι × κ) (ι × κ) ℂ) : ptFirst (ρ + σ) = ptFirst ρ + ptFirst σ := by
  ext ⟨i, k⟩ ⟨j, l⟩; rfl

theorem ptFirst_sub (ρ σ : Matrix (ι × κ) (ι × κ) ℂ) : ptFirst (ρ - σ) = ptFirst ρ - ptFirst σ := by
  ext ⟨i, k⟩ ⟨j, l⟩; rfl

theorem ptFirst_smul (c : ℂ) (ρ : Matrix (ι × κ) (ι × κ) ℂ) : ptFirst (c • ρ) = c • ptFirst ρ := by
  ext ⟨i, k⟩ ⟨j, l⟩; rfl

theorem ptFirst_prodRankOne (a : ι → ℂ) (b : κ → ℂ) :
    ptFirst (prodRankOne a b) = prodRankOne (star a) b := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [ptFirst_apply, prodRankOne, kronecker_apply, vecMulVec_apply, Pi.star_apply,
    star_star]
  ring

theorem ptFirst_congr (S : Matrix ι ι ℂ) (T : Matrix κ κ ℂ) (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    ptFirst ((S ⊗ₖ T) * ρ * (S ⊗ₖ T)ᴴ) =
      (S.map star ⊗ₖ T) * ptFirst ρ * (S.map star ⊗ₖ T)ᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [ptFirst_apply, mul_apply, kronecker_apply, conjTranspose_apply, Fintype.sum_prod_type,
    map_apply, Finset.sum_mul, star_mul']
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; enter [2, x1]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [star_star]
  ring


theorem posSemidef_sub_schur {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (f : n → ℂ) :
    (M - (star f ⬝ᵥ M *ᵥ f)⁻¹ • vecMulVec (M *ᵥ f) (star (M *ᵥ f))).PosSemidef := by
  set c := star f ⬝ᵥ M *ᵥ f with hc
  by_cases hc0 : c = 0
  · have : M *ᵥ f = 0 := hM.dotProduct_mulVec_zero_iff.1 hc0
    simpa [this, hc0] using hM
  · have hcnn : 0 ≤ c := hM.dotProduct_mulVec_nonneg f
    have hcre : star c = c := by
      have := (Complex.nonneg_iff.1 hcnn).2
      apply Complex.ext <;> simp [← this]
    have hw : star f ᵥ* M = star (M *ᵥ f) := by
      rw [star_mulVec, hM.isHermitian.eq]
    have hcf : star f ⬝ᵥ (M *ᵥ f) = c := rfl
    have key : (1 - c⁻¹ • vecMulVec f (star (M *ᵥ f)))ᴴ * M *
        (1 - c⁻¹ • vecMulVec f (star (M *ᵥ f))) =
        M - c⁻¹ • vecMulVec (M *ᵥ f) (star (M *ᵥ f)) := by
      have h1 : (1 - c⁻¹ • vecMulVec f (star (M *ᵥ f)))ᴴ =
          1 - c⁻¹ • vecMulVec (M *ᵥ f) (star f) := by
        rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec,
          star_star, star_inv₀, hcre]
      have hWu : vecMulVec (M *ᵥ f) (star (M *ᵥ f)) * vecMulVec f (star (M *ᵥ f)) =
          c • vecMulVec (M *ᵥ f) (star (M *ᵥ f)) := by
        have hd : star (M *ᵥ f) ⬝ᵥ f = c := by
          rw [star_mulVec, hM.isHermitian.eq, ← dotProduct_mulVec]
        rw [vecMulVec_mul_vecMulVec, hd, vecMulVec_smul]
      have hMu : M * vecMulVec f (star (M *ᵥ f)) = vecMulVec (M *ᵥ f) (star (M *ᵥ f)) :=
        mul_vecMulVec _ _ _
      have e1 : (1 - c⁻¹ • vecMulVec (M *ᵥ f) (star f)) * M =
          M - c⁻¹ • vecMulVec (M *ᵥ f) (star (M *ᵥ f)) := by
        rw [sub_mul, one_mul, smul_mul, vecMulVec_mul, hw]
      have e2 : (M - c⁻¹ • vecMulVec (M *ᵥ f) (star (M *ᵥ f))) *
          vecMulVec f (star (M *ᵥ f)) = 0 := by
        rw [sub_mul, smul_mul, hMu, hWu, smul_smul, inv_mul_cancel₀ hc0, one_smul, sub_self]
      rw [h1, Matrix.mul_assoc, ← Matrix.mul_assoc _ M, e1, mul_sub, mul_one, Matrix.mul_smul, e2,
        smul_zero, sub_zero]
    rw [← key]
    exact hM.conjTranspose_mul_mul_same _


theorem exists_isUnit_mulVec_single {n : Type*} [Fintype n] [DecidableEq n] (x : n → ℂ)
    (hx : x ≠ 0) (i : n) : ∃ V : Matrix n n ℂ, IsUnit V.det ∧ V *ᵥ Pi.single i 1 = x := by
  obtain ⟨m, hm⟩ : ∃ m, x m ≠ 0 := by
    by_contra h; exact hx (funext fun m => by_contra fun h' => h ⟨m, h'⟩)
  set σ := Equiv.swap i m with hσ
  set x' : n → ℂ := fun k => x (σ k) with hx'
  refine ⟨((1 : Matrix n n ℂ).updateCol i x').submatrix σ id, ?_, ?_⟩
  · rw [det_permute]
    have h1 : ((1 : Matrix n n ℂ).updateCol i x').det = x' i := by
      have := det_updateCol_sum (1 : Matrix n n ℂ) i x'
      simpa [Matrix.one_apply, Finset.sum_ite_eq'] using this
    rw [h1]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [hx', hσ, hm]
  · ext r
    simp [hx', hσ]


/-- Local congruence `X ↦ (S ⊗ T) X (S ⊗ T)ᴴ` preserves separability. -/
theorem isSeparable_congr (S : Matrix ι ι ℂ) (T : Matrix κ κ ℂ) {X : Matrix (ι × κ) (ι × κ) ℂ}
    (hX : IsSeparable X) : IsSeparable ((S ⊗ₖ T) * X * (S ⊗ₖ T)ᴴ) := by
  obtain ⟨N, a, b, rfl⟩ := hX
  refine ⟨N, fun i => S *ᵥ a i, fun i => T *ᵥ b i, ?_⟩
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [prodRankOne, conjTranspose_kronecker, ← mul_kronecker_mul]
  congr 1 <;> rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- **Hypothesis** (Horodecki–Horodecki–Horodecki 1996; not in Mathlib, proved in `PPTSeparable23.lean`
from the vendored math-lab development as `pptSeparable23`): every positive operator on
`ℂ² ⊗ ℂ³` with positive semidefinite partial transpose is separable.  It is the only external input of
`ppt_product_kernel`. -/
def PPTSeparable23 : Prop :=
  ∀ ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ, ρ.PosSemidef → (ptFirst ρ).PosSemidef →
    IsSeparable ρ

theorem prodRankOne_apply (a : ι → ℂ) (b : κ → ℂ) (i j : ι) (k l : κ) :
    prodRankOne a b (i, k) (j, l) = a i * star (a j) * (b k * star (b l)) := by
  simp [prodRankOne, vecMulVec_apply]

theorem prodRankOne_apply' (a : ι → ℂ) (b : κ → ℂ) (p q : ι × κ) :
    prodRankOne a b p q = a p.1 * star (a q.1) * (b p.2 * star (b q.2)) :=
  prodRankOne_apply a b p.1 q.1 p.2 q.2

/-- Extension by zero of a vector on `Fin 3` to `Fin 4`. -/
def extZero (b : Fin 3 → ℂ) : Fin 4 → ℂ := Fin.snoc (α := fun _ => ℂ) b 0

theorem extZero_castSucc (b : Fin 3 → ℂ) (k : Fin 3) : extZero b (Fin.castSucc k) = b k := by
  simp [extZero]

theorem extZero_three (b : Fin 3 → ℂ) : extZero b 3 = 0 := by
  simp [extZero, Fin.snoc]

/-- A PPT operator on `ℂ² ⊗ ℂ⁴` whose kernel contains `|j, 3⟩` for `j = 0, 1` lives on `ℂ² ⊗ ℂ³`, so
it is separable under `PPTSeparable23`. -/
theorem sep_of_supported (h : PPTSeparable23) (σ : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)
    (hσ : σ.PosSemidef) (hT : (ptFirst σ).PosSemidef)
    (hz : ∀ j : Fin 2, σ *ᵥ Pi.single (j, (3 : Fin 4)) 1 = 0) : IsSeparable σ := by
  have hcol : ∀ (p : Fin 2 × Fin 4) (j : Fin 2), σ p (j, 3) = 0 := fun p j => by
    simpa [mulVec_single_one] using congrFun (hz j) p
  have hrow : ∀ (j : Fin 2) (q : Fin 2 × Fin 4), σ (j, 3) q = 0 := fun j q => by
    have := hσ.isHermitian.apply (j, 3) q
    rw [← this]; simp [hcol]
  let emb : Fin 2 × Fin 3 → Fin 2 × Fin 4 := fun p => (p.1, Fin.castSucc p.2)
  have h1 : (σ.submatrix emb emb).PosSemidef := hσ.submatrix emb
  have h2 : (ptFirst (σ.submatrix emb emb)).PosSemidef := by
    have : ptFirst (σ.submatrix emb emb) = (ptFirst σ).submatrix emb emb := rfl
    rw [this]; exact hT.submatrix emb
  obtain ⟨N, a, b, hab⟩ := h _ h1 h2
  refine ⟨N, a, fun i => extZero (b i), ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sum_apply, prodRankOne_apply]
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · have : σ (i, 3) (j, l) = 0 := hrow i _
    simp [this, extZero_three]
  refine Fin.lastCases ?_ (fun l' => ?_) l
  · have : σ (i, Fin.castSucc k') (j, 3) = 0 := hcol _ j
    simp [this, extZero_three]
  · have := congrFun (congrFun hab (i, k')) (j, l')
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, prodRankOne_apply, emb] at this
    simpa only [extZero_castSucc] using this

theorem mulVec_single_apply {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (j p : n) :
    (M *ᵥ Pi.single j (1 : ℂ)) p = M p j := by
  simp

/-- The product-kernel lemma with the kernel vector normalised to `|0, 3⟩`. -/
theorem sep_of_kernel_basis (h : PPTSeparable23) (ρ : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptFirst ρ).PosSemidef)
    (hk : ρ *ᵥ Pi.single ((0 : Fin 2), (3 : Fin 4)) 1 = 0) : IsSeparable ρ := by
  have hcol0 : ∀ p, ρ p (0, 3) = 0 := fun p => by
    simpa [mulVec_single_apply] using congrFun hk p
  have hTcol : ptFirst ρ *ᵥ Pi.single ((0 : Fin 2), (3 : Fin 4)) 1 = 0 := by
    rw [← hT.dotProduct_mulVec_zero_iff]
    simp [ptFirst_apply, hcol0]
  have hB : ∀ k, ρ (0, k) (1, 3) = 0 := fun k => by
    have := congrFun hTcol (1, k)
    rw [mulVec_single_apply, ptFirst_apply] at this
    exact this
  set w : Fin 2 × Fin 4 → ℂ := ρ *ᵥ Pi.single ((1 : Fin 2), (3 : Fin 4)) 1 with hw
  have hwp : ∀ p, w p = ρ p (1, 3) := fun p => mulVec_single_apply _ _ _
  have hw0 : ∀ k, w (0, k) = 0 := fun k => by rw [hwp]; exact hB k
  have hptw : ptFirst ρ *ᵥ Pi.single ((1 : Fin 2), (3 : Fin 4)) 1 = w := by
    ext ⟨i, k⟩
    rw [hwp, mulVec_single_apply, ptFirst_apply]
    fin_cases i
    · exact (hcol0 _).trans (hB k).symm
    · rfl
  set c : ℂ := star (Pi.single ((1 : Fin 2), (3 : Fin 4)) (1 : ℂ) : Fin 2 × Fin 4 → ℂ) ⬝ᵥ
    ρ *ᵥ Pi.single ((1 : Fin 2), (3 : Fin 4)) 1 with hc
  have hcw : c = w (1, 3) := by simp [hc, ← hw]
  have hc2 : star (Pi.single ((1 : Fin 2), (3 : Fin 4)) (1 : ℂ) : Fin 2 × Fin 4 → ℂ) ⬝ᵥ
      ptFirst ρ *ᵥ Pi.single ((1 : Fin 2), (3 : Fin 4)) 1 = c := by
    rw [hptw, hcw]; simp
  have hptW : ptFirst (vecMulVec w (star w)) = vecMulVec w (star w) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [ptFirst_apply]
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, hw0]
  set ρ' := ρ - c⁻¹ • vecMulVec w (star w) with hρ'
  have hρ'psd : ρ'.PosSemidef := posSemidef_sub_schur hρ _
  have hT' : (ptFirst ρ').PosSemidef := by
    have := posSemidef_sub_schur hT (Pi.single ((1 : Fin 2), (3 : Fin 4)) (1 : ℂ))
    rw [hc2, hptw] at this
    rw [hρ', ptFirst_sub, ptFirst_smul, hptW]
    exact this
  have hcnn : 0 ≤ c := by rw [hc]; exact hρ.dotProduct_mulVec_nonneg _
  have hcim : c.im = 0 := (Complex.nonneg_iff.1 hcnn).2.symm
  have hcre : star c = c := by apply Complex.ext <;> simp [hcim]
  have hw3 : w (0, 3) = 0 := hw0 3
  have hcz : c = 0 → w = 0 := fun hc0 =>
    hρ.dotProduct_mulVec_zero_iff.1 (by rw [← hc]; exact hc0)
  have hzero : ∀ j : Fin 2, ρ' *ᵥ Pi.single (j, (3 : Fin 4)) 1 = 0 := by
    intro j; ext p
    rw [mulVec_single_apply, hρ', Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      Pi.zero_apply]
    by_cases hc0 : c = 0
    · have hw00 := hcz hc0
      fin_cases j
      · simp [hcol0, hw3]
      · simp [← hwp, hw00]
    · fin_cases j
      · simp [hcol0, hw3]
      · simp only [Fin.mk_one, Fin.isValue, Pi.star_apply, smul_eq_mul]
        rw [← hwp p, ← hcw, hcre]
        field_simp
        ring
  have hsepρ' : IsSeparable ρ' := sep_of_supported h ρ' hρ'psd hT' hzero
  have hsepW : IsSeparable (c⁻¹ • vecMulVec w (star w)) := by
    by_cases hc0 : c = 0
    · simp [hcz hc0, isSeparable_zero]
    · have hwab : w = kroneckerVec (Pi.single (1 : Fin 2) (1 : ℂ)) (fun k => w (1, k)) := by
        ext ⟨i, k⟩
        fin_cases i <;> simp [kroneckerVec, hw0]
      have hr : c⁻¹ • vecMulVec w (star w) =
          ((c.re)⁻¹ : ℝ) • prodRankOne (Pi.single (1 : Fin 2) (1 : ℂ)) (fun k => w (1, k)) := by
        rw [prodRankOne_eq, ← hwab]
        have : c⁻¹ = (((c.re)⁻¹ : ℝ) : ℂ) := by
          have hcc : c = (c.re : ℂ) := Complex.ext (by simp) (by simp [hcim])
          rw [hcc]; simp
        rw [this, ← Complex.coe_smul]
      rw [hr]
      exact (isSeparable_prodRankOne _ _).smul_nonneg (inv_nonneg.2 (Complex.nonneg_iff.1 hcnn).1)
  have hdecomp : ρ = ρ' + c⁻¹ • vecMulVec w (star w) := by rw [hρ']; abel
  rw [hdecomp]
  exact hsepρ'.add hsepW

/-- **Product-kernel lemma** (`lem:ppt3-product-kernel`, first sentence; source
`appendix_moment_cone.tex`).  A positive operator `ρ` on `ℂ² ⊗ ℂ⁴` whose partial transpose is positive
semidefinite and whose kernel contains a nonzero product vector `a ⊗ b` is separable.

**Hypothesis:** `PPTSeparable23`, the Horodecki–Horodecki–Horodecki (1996) theorem that PPT operators on
`ℂ² ⊗ ℂ³` are separable, which is not in Mathlib; it is proved from the vendored math-lab development as `pptSeparable23`,
and `ppt_product_kernel'` is this statement without the hypothesis.  The paper's local-unitary
normalisation `a ⊗ b ↦ |0, 3⟩` is done here with local invertible congruences `(Vᴴ ⊗ Wᴴ) · (…)`.
Not covered here: the three-qubit consequence (see `ProductKernelThree`). -/
theorem ppt_product_kernel (h : PPTSeparable23) (ρ : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)
    (hρ : ρ.PosSemidef) (hT : (ptFirst ρ).PosSemidef) (a : Fin 2 → ℂ) (b : Fin 4 → ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hk : ρ *ᵥ kroneckerVec a b = 0) : IsSeparable ρ := by
  obtain ⟨V, hV, hVa⟩ := exists_isUnit_mulVec_single a ha 0
  obtain ⟨W, hW, hWb⟩ := exists_isUnit_mulVec_single b hb 3
  have hV' : V * V⁻¹ = 1 := mul_nonsing_inv V hV
  have hW' : W * W⁻¹ = 1 := mul_nonsing_inv W hW
  set X : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ := Vᴴ ⊗ₖ Wᴴ with hX
  set Y : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ := (V⁻¹)ᴴ ⊗ₖ (W⁻¹)ᴴ with hY
  have hYX : Y * X = 1 := by
    rw [hX, hY, ← mul_kronecker_mul, ← conjTranspose_mul, ← conjTranspose_mul, hV', hW',
      conjTranspose_one, conjTranspose_one, one_kronecker_one]
  have hρ' : (X * ρ * Xᴴ).PosSemidef := hρ.mul_mul_conjTranspose_same X
  have hT' : (ptFirst (X * ρ * Xᴴ)).PosSemidef := by
    rw [hX, ptFirst_congr]
    exact hT.mul_mul_conjTranspose_same _
  have hVi : ∀ i, V i 0 = a i := fun i => by rw [← hVa, mulVec_single_apply]
  have hWk : ∀ k, W k 3 = b k := fun k => by rw [← hWb, mulVec_single_apply]
  have hXe : Xᴴ *ᵥ Pi.single ((0 : Fin 2), (3 : Fin 4)) 1 = kroneckerVec a b := by
    ext ⟨i, k⟩
    rw [mulVec_single_apply, hX, conjTranspose_kronecker]
    simp only [conjTranspose_conjTranspose]
    rw [kronecker_apply, hVi, hWk, kroneckerVec]
  have hker : (X * ρ * Xᴴ) *ᵥ Pi.single ((0 : Fin 2), (3 : Fin 4)) 1 = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hXe, hk, mulVec_zero]
  have hsep := isSeparable_congr (V⁻¹)ᴴ (W⁻¹)ᴴ (sep_of_kernel_basis h _ hρ' hT' hker)
  have hρeq : Y * (X * ρ * Xᴴ) * Yᴴ = ρ := by
    calc Y * (X * ρ * Xᴴ) * Yᴴ = (Y * X) * ρ * (Xᴴ * Yᴴ) := by simp only [Matrix.mul_assoc]
      _ = ρ := by rw [← conjTranspose_mul, hYX, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [← hρeq]
  exact hsep

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.ppt_product_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.ppt_product_kernel
