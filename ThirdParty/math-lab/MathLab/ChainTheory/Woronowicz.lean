module

/-
Woronowicz.lean

**Woronowicz's theorem** (S. L. Woronowicz, Rep. Math. Phys. 10 (1976) 165): every positive linear
map M₂(ℂ) → M₃(ℂ) is decomposable. With it the alpha Letter's read cap holds for its own readability
with no hypothesis (`readcap`).

The proof is in state form and follows Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman, Oper.
Matrices 3 (2009), Thm 5.2, with Krein–Milman in place of their extreme-ray decomposition:
  1. On an extreme ray of the PPT cone of ℂ² ⊗ ℂ³, `r² + s² ≤ 37` for the ranks of ρ and ρ^Γ
     (`PPTFace.lean`).
  2. If the reduced operator on ℂ³ is singular, ρ lives on ℂ² ⊗ ℂ² and is separable by the two-qubit
     theorem (Physical Superintelligence's `twoQubit_ppt_separable`, through `Stormer.lean`).
  3. Otherwise a local operation brings ρ to `[[1, B], [Bᴴ, C]]`. The bound leaves three cases:
     `C = BᴴB`, `C = BBᴴ`, or both Schur complements of rank one. In each, B has a normal dilation N
     with `C ⪰ (N Nᴴ)₁₁` (`NormalCompletion.lean`, KSW Thm 2.4 in the third case), and then ρ is
     separable (`sep_of_normal_dilation`).
  4. Krein–Milman: the trace-one PPT operators are the closed convex hull of their extreme points, so
     every PPT operator pairs nonnegatively with the Choi matrix of every positive map, and the
     separation argument of `Duality.lean` gives decomposability.
-/
public import MathLab.ChainTheory.PPTFace
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

open Matrix ComplexOrder Module
open scoped Kronecker

noncomputable section

namespace ChainWoronowicz

open ChoiDark ChainReadCap ChainDuality ChainStormer

variable {m : ℕ}

/-! ## Positive matrices -/

theorem isPSD_mulVec_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hP : IsPSD P) {v : ι → ℂ} (h : star v ⬝ᵥ (P *ᵥ v) = 0) : P *ᵥ v = 0 := by
  obtain ⟨F, rfl⟩ := hP.gram
  have h1 : star (F *ᵥ v) ⬝ᵥ (F *ᵥ v) = 0 := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    exact h
  rw [← mulVec_mulVec, dotProduct_star_self_eq_zero.1 h1, mulVec_zero]

theorem isPSD_transpose {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (h : IsPSD M) : IsPSD Mᵀ := by
  intro w
  have e : star w ⬝ᵥ (Mᵀ *ᵥ w) = star (star w) ⬝ᵥ (M *ᵥ star w) := by
    simp only [dotProduct, mulVec, transpose_apply, star_star, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  exact h _

theorem isPSD_of_transpose {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (h : IsPSD Mᵀ) : IsPSD M := by
  simpa using isPSD_transpose h

theorem eq_zero_of_isPSD_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (h : IsPSD M) (htr : M.trace = 0) : M = 0 := by
  obtain ⟨F, rfl⟩ := h.gram
  rw [trace_conjTranspose_mul_self_eq_zero_iff.1 htr, Matrix.mul_zero]

/-- The Schur complement of `[[1, B], [Bᴴ, C]] ⪰ 0` is `C - Bᴴ B ⪰ 0`. -/
theorem isPSD_schur {B C : Matrix (Fin m) (Fin m) ℂ} (h : IsPSD (blk 1 B Bᴴ C)) :
    IsPSD (C - Bᴴ * B) := by
  intro w
  have e : star w ⬝ᵥ ((C - Bᴴ * B) *ᵥ w) =
      star (bvec (-(B *ᵥ w)) w) ⬝ᵥ (blk 1 B Bᴴ C *ᵥ bvec (-(B *ᵥ w)) w) := by
    rw [blk_mulVec_bvec, star_bvec_dotProduct, one_mulVec, neg_add_cancel, dotProduct_zero,
      zero_add, mulVec_neg, mulVec_mulVec, sub_mulVec, neg_add_eq_sub]
  rw [e]
  exact h _

theorem conjTranspose_transpose' (B : Matrix (Fin m) (Fin m) ℂ) : (Bᵀ)ᴴ = (Bᴴ)ᵀ := rfl

/-- The Schur complement of the partial transpose: `(C - B Bᴴ)ᵀ ⪰ 0`. -/
theorem isPSD_schur_pt {B C : Matrix (Fin m) (Fin m) ℂ} (h : IsPSD (pt (blk 1 B Bᴴ C))) :
    IsPSD (C - B * Bᴴ)ᵀ := by
  rw [pt_blk, transpose_one, ← conjTranspose_transpose'] at h
  have h2 := isPSD_schur h
  rwa [conjTranspose_transpose', ← transpose_mul, ← transpose_sub] at h2

/-- A Gram factor `S = Gᴴ G`, a basis `b` of the range of `Gᴴ`, and what its size says about `S`. -/
theorem psd_basis {S : Matrix (Fin m) (Fin m) ℂ} (hS : IsPSD S) :
    ∃ (G : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) (b : Fin k → Fin m → ℂ), S = Gᴴ * G ∧
      LinearIndependent ℂ b ∧ (∀ j, ∃ c, b j = Gᴴ *ᵥ c) ∧ (k = 0 → S = 0) ∧
      (k = 1 → ∃ y, S = vecMulVec y (star y)) := by
  obtain ⟨G, hG⟩ := hS.gram
  set R := LinearMap.range (Gᴴ).mulVecLin with hR
  set bas := Module.finBasis ℂ R with hbas
  have hcol : ∀ j, Gᴴ *ᵥ Pi.single j 1 ∈ R := fun j => LinearMap.mem_range_self _ _
  have hGG : S = Gᴴ * (Gᴴ)ᴴ := by rw [conjTranspose_conjTranspose, hG]
  refine ⟨G, finrank ℂ R, fun j => (bas j : Fin m → ℂ), hG, ?_, ?_, ?_, ?_⟩
  · exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro j
    obtain ⟨c, hc⟩ := (bas j).2
    exact ⟨c, hc.symm⟩
  · intro hk
    have hR0 : R = ⊥ := Submodule.finrank_eq_zero.1 hk
    have hGH : Gᴴ = 0 := by
      ext i j
      have h := hcol j
      rw [hR0, Submodule.mem_bot] at h
      have := congrFun h i
      simpa [mulVec_single_one] using this
    rw [hGG, hGH, Matrix.zero_mul]
  · intro hk
    have h0 : (0 : ℕ) < finrank ℂ R := by omega
    set b0 : R := bas ⟨0, h0⟩ with hb0
    have hne : b0 ≠ 0 := bas.ne_zero _
    have hspan := (finrank_eq_one_iff_of_nonzero' b0 hne).1 hk
    have hc : ∀ j, ∃ c : ℂ, c • (b0 : Fin m → ℂ) = Gᴴ *ᵥ Pi.single j 1 := by
      intro j
      obtain ⟨c, hc⟩ := hspan ⟨_, hcol j⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    choose c hc using hc
    have hGH : Gᴴ = vecMulVec (b0 : Fin m → ℂ) c := by
      ext i j
      have := congrFun (hc j) i
      simp only [Pi.smul_apply, smul_eq_mul, mulVec_single_one, col_apply] at this
      rw [vecMulVec_apply, ← this, mul_comm]
    have hcc : ((Real.sqrt (∑ j, ‖c j‖ ^ 2) : ℝ) : ℂ) * star ((Real.sqrt (∑ j, ‖c j‖ ^ 2) : ℝ) : ℂ) =
        ∑ j, c j * star (c j) := by
      rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      push_cast
      exact Finset.sum_congr rfl fun j _ => (Complex.mul_conj' (c j)).symm
    refine ⟨((Real.sqrt (∑ j, ‖c j‖ ^ 2) : ℝ) : ℂ) • (b0 : Fin m → ℂ), ?_⟩
    rw [hGG, hGH]
    ext i l
    simp only [Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Pi.star_apply, star_mul']
    calc ∑ x, (b0 : Fin m → ℂ) i * c x * (star ((b0 : Fin m → ℂ) l) * star (c x))
        = (b0 : Fin m → ℂ) i * star ((b0 : Fin m → ℂ) l) * ∑ x, c x * star (c x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [← hcc]; ring

/-! ## The normalized base case -/

/-- **On an extreme ray, `[[1, B], [Bᴴ, C]]` on `ℂ² ⊗ ℂ³` is separable.** -/
theorem sep_of_extreme_normalized {B C : Matrix (Fin 3) (Fin 3) ℂ}
    (hρ : IsExtremePPT (blk 1 B Bᴴ C)) : IsSeparable (blk 1 B Bᴴ C) := by
  have hS := isPSD_schur hρ.1.1
  have hS' := isPSD_schur_pt hρ.1.2
  obtain ⟨G, k, b, hG, hb, hbG, hk0, hk1⟩ := psd_basis hS
  obtain ⟨G', k', b', hG', hb', hbG', hk0', hk1'⟩ := psd_basis hS'
  -- Gram factors of ρ and of its partial transpose
  have hF : blk 1 B Bᴴ C = (blk 1 B 0 G)ᴴ * blk 1 B 0 G := by
    rw [blk_conjTranspose, blk_mul, ← hG]
    simp
  have hF' : pt (blk 1 B Bᴴ C) = (blk 1 Bᵀ 0 G')ᴴ * blk 1 Bᵀ 0 G' := by
    have e : (C - B * Bᴴ)ᵀ = Cᵀ - (Bᵀ)ᴴ * Bᵀ := by
      rw [transpose_sub, transpose_mul, conjTranspose_transpose']
    rw [pt_blk, blk_conjTranspose, blk_mul, ← hG', e]
    simp [conjTranspose_transpose']
  -- independent vectors in the ranges of the Gram factors
  set u : Fin 3 ⊕ Fin k → Idx 2 3 → ℂ :=
    Sum.elim (fun j => bvec (Pi.single j 1) (Bᴴ *ᵥ Pi.single j 1)) (fun j => bvec 0 (b j)) with hu_def
  set v : Fin 3 ⊕ Fin k' → Idx 2 3 → ℂ :=
    Sum.elim (fun j => bvec (Pi.single j 1) ((Bᵀ)ᴴ *ᵥ Pi.single j 1)) (fun j => bvec 0 (b' j))
    with hv_def
  have hind : ∀ {k : ℕ} (b : Fin k → Fin 3 → ℂ) (D : Matrix (Fin 3) (Fin 3) ℂ),
      LinearIndependent ℂ b → LinearIndependent ℂ
        (Sum.elim (fun j => bvec (Pi.single j 1) (D *ᵥ Pi.single j 1)) (fun j => bvec 0 (b j)) :
          Fin 3 ⊕ Fin k → Idx 2 3 → ℂ) := by
    intro k b D hb
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∀ j, g (Sum.inl j) = 0 := by
      intro j
      have := congrFun hg (0, j)
      simpa [bvec, Fintype.sum_sum_type, Pi.single_apply, Finset.sum_apply] using this
    have h1 : ∑ l, g (Sum.inr l) • b l = 0 := by
      ext x
      have := congrFun hg (1, x)
      simpa [bvec, Fintype.sum_sum_type, h0, Finset.sum_apply] using this
    have h2 := Fintype.linearIndependent_iff.1 hb _ h1
    rintro (j | l)
    · exact h0 j
    · exact h2 l
  have hu' : ∀ i, ∃ w, u i = (blk 1 B 0 G)ᴴ *ᵥ w := by
    rintro (j | l)
    · exact ⟨bvec (Pi.single j 1) 0, by
        rw [blk_conjTranspose, blk_mulVec_bvec, conjTranspose_one, one_mulVec]; simp [hu_def]⟩
    · obtain ⟨c, hc⟩ := hbG l
      exact ⟨bvec 0 c, by rw [blk_conjTranspose, blk_mulVec_bvec]; simp [hu_def, hc]⟩
  have hv' : ∀ i, ∃ w, v i = (blk 1 Bᵀ 0 G')ᴴ *ᵥ w := by
    rintro (j | l)
    · exact ⟨bvec (Pi.single j 1) 0, by
        rw [blk_conjTranspose, blk_mulVec_bvec, conjTranspose_one, one_mulVec]; simp [hv_def]⟩
    · obtain ⟨c, hc⟩ := hbG' l
      exact ⟨bvec 0 c, by rw [blk_conjTranspose, blk_mulVec_bvec]; simp [hv_def, hc]⟩
  have hbound := extreme_rank_bound hρ _ _ hF hF' (u ∘ finSumFinEquiv.symm)
    ((hind b Bᴴ hb).comp _ finSumFinEquiv.symm.injective) (fun i => hu' _)
    (v ∘ finSumFinEquiv.symm) ((hind b' (Bᵀ)ᴴ hb').comp _ finSumFinEquiv.symm.injective)
    (fun i => hv' _)
  have hk : k = 0 ∨ k' = 0 ∨ (k = 1 ∧ k' = 1) := by
    have hk3 : k ≤ 3 := by nlinarith
    have hk3' : k' ≤ 3 := by nlinarith
    interval_cases k <;> interval_cases k' <;> omega
  -- in every case: C = B Bᴴ + x xᴴ and Bᴴ B - B Bᴴ = x xᴴ - y yᴴ
  obtain ⟨x, y, hC, hD⟩ : ∃ x y : Fin 3 → ℂ, C = B * Bᴴ + vecMulVec x (star x) ∧
      Bᴴ * B - B * Bᴴ = vecMulVec x (star x) - vecMulVec y (star y) := by
    rcases hk with h | h | ⟨h, h'⟩
    · have hCB : C = Bᴴ * B := sub_eq_zero.1 (hk0 h)
      have hN : Bᴴ * B - B * Bᴴ = 0 := by
        apply eq_zero_of_isPSD_trace
        · have := isPSD_of_transpose hS'
          rwa [hCB] at this
        · rw [trace_sub, trace_mul_comm, sub_self]
      refine ⟨0, 0, ?_, ?_⟩
      · rw [hCB, sub_eq_zero.1 hN]
        simp
      · rw [hN]
        simp
    · have hCB : C = B * Bᴴ := by
        have h0 : (C - B * Bᴴ)ᵀ = 0 := hk0' h
        have : C - B * Bᴴ = 0 := by
          rw [← transpose_transpose (C - B * Bᴴ), h0, transpose_zero]
        exact sub_eq_zero.1 this
      have hN : B * Bᴴ - Bᴴ * B = 0 := by
        apply eq_zero_of_isPSD_trace
        · rwa [hCB] at hS
        · rw [trace_sub, trace_mul_comm, sub_self]
      refine ⟨0, 0, ?_, ?_⟩
      · rw [hCB]
        simp
      · rw [← neg_sub, hN]
        simp
    · obtain ⟨y, hy⟩ := hk1 h
      obtain ⟨x', hx'⟩ := hk1' h'
      have hx : C - B * Bᴴ = vecMulVec (star x') (star (star x')) := by
        rw [← transpose_transpose (C - B * Bᴴ), hx']
        ext i j
        simp [vecMulVec_apply, mul_comm]
      refine ⟨star x', y, ?_, ?_⟩
      · rw [← hx]
        abel
      · rw [← hx, ← hy]
        abel
  obtain ⟨N, w, hN, hN11, hNC⟩ := MathLab.exists_normal_dilation B x y hD
  have hsep := sep_of_normal_dilation N hN C (by rw [hC, hNC]; exact isPSD_rank_one w)
  rwa [hN11] at hsep

/-! ## Reduction 1: a common kernel vector of the diagonal blocks -/

theorem quad_bvec_left (ρ : Mat 2 m) (w : Fin m → ℂ) :
    star (bvec w 0) ⬝ᵥ (ρ *ᵥ bvec w 0) = star w ⬝ᵥ (blkOf ρ 0 0 *ᵥ w) := by
  conv_lhs => rw [← blk_blkOf ρ]
  rw [blk_mulVec_bvec, star_bvec_dotProduct]
  simp

theorem quad_bvec_right (ρ : Mat 2 m) (w : Fin m → ℂ) :
    star (bvec 0 w) ⬝ᵥ (ρ *ᵥ bvec 0 w) = star w ⬝ᵥ (blkOf ρ 1 1 *ᵥ w) := by
  conv_lhs => rw [← blk_blkOf ρ]
  rw [blk_mulVec_bvec, star_bvec_dotProduct]
  simp

theorem isPSD_blkOf_00 {ρ : Mat 2 m} (h : IsPSD ρ) : IsPSD (blkOf ρ 0 0) := fun w => by
  rw [← quad_bvec_left]
  exact h _

theorem isPSD_blkOf_11 {ρ : Mat 2 m} (h : IsPSD ρ) : IsPSD (blkOf ρ 1 1) := fun w => by
  rw [← quad_bvec_right]
  exact h _

/-- `ρ (I ⊗ w wᴴ) = 0` when `ρ` kills `e_b ⊗ w` for both `b`. -/
theorem mul_kron_eq_zero {ρ : Mat 2 m} {w : Fin m → ℂ} (h0 : ρ *ᵥ bvec w 0 = 0)
    (h1 : ρ *ᵥ bvec 0 w = 0) : ρ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ vecMulVec w (star w)) = 0 := by
  have hb : ∀ b : Fin 2, ∀ x, ∑ p, ρ x (b, p) * w p = 0 := by
    intro b x
    fin_cases b
    · have := congrFun h0 x
      simpa [mulVec, dotProduct, bvec, Fintype.sum_prod_type, Fin.sum_univ_two] using this
    · have := congrFun h1 x
      simpa [mulVec, dotProduct, bvec, Fintype.sum_prod_type, Fin.sum_univ_two] using this
  ext x ⟨b, l⟩
  simp only [Matrix.mul_apply, kroneckerMap_apply, one_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, Matrix.zero_apply]
  have : ∀ c : Fin 2, ∑ p, ρ x (c, p) * ((if c = b then 1 else 0) * (w p * star (w l))) =
      (if c = b then 1 else 0) * star (w l) * ∑ p, ρ x (c, p) * w p := by
    intro c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [this, hb, mul_zero, Finset.sum_const_zero]

/-- **Compression**: if `ρ ⪰ 0` on `ℂ² ⊗ ℂᵏ⁺¹` and `(ρ₀₀ + ρ₁₁) w = 0` for some `w ≠ 0`, then ρ lives
on `ℂ² ⊗ w^⊥`: for an isometry `V` onto `w^⊥`, `ρ = (1 ⊗ V)(1 ⊗ V)ᴴ ρ (1 ⊗ V)(1 ⊗ V)ᴴ`. -/
theorem exists_compress {k : ℕ} {ρ : Mat 2 (k + 1)} (hρ : IsPSD ρ) {w : Fin (k + 1) → ℂ} (hw : w ≠ 0)
    (hk : (blkOf ρ 0 0 + blkOf ρ 1 1) *ᵥ w = 0) :
    ∃ V : Matrix (Fin (k + 1)) (Fin k) ℂ,
      lop (1 : Matrix (Fin 2) (Fin 2) ℂ) V (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ) = ρ := by
  have hq : star w ⬝ᵥ (blkOf ρ 0 0 *ᵥ w) + star w ⬝ᵥ (blkOf ρ 1 1 *ᵥ w) = 0 := by
    rw [← dotProduct_add, ← add_mulVec, hk, dotProduct_zero]
  have h0 := isPSD_blkOf_00 hρ w
  have h1 := isPSD_blkOf_11 hρ w
  have hre := congrArg Complex.re hq
  rw [Complex.add_re, Complex.zero_re] at hre
  have hq0 : star w ⬝ᵥ (blkOf ρ 0 0 *ᵥ w) = 0 := Complex.ext (by simp; linarith [h0.1, h1.1]) h0.2
  have hq1 : star w ⬝ᵥ (blkOf ρ 1 1 *ᵥ w) = 0 := Complex.ext (by simp; linarith [h0.1, h1.1]) h1.2
  have hk0 : ρ *ᵥ bvec w 0 = 0 := isPSD_mulVec_eq_zero hρ (by rw [quad_bvec_left]; exact hq0)
  have hk1 : ρ *ᵥ bvec 0 w = 0 := isPSD_mulVec_eq_zero hρ (by rw [quad_bvec_right]; exact hq1)
  -- an orthonormal basis of ℂᵏ⁺¹ whose last vector is w / ‖w‖
  set c : ℂ := ((‖WithLp.toLp 2 w‖ : ℝ) : ℂ)⁻¹ with hc
  have hwn : ‖WithLp.toLp 2 w‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    exact hw (by simpa using congrArg WithLp.ofLp h)
  set u : EuclideanSpace ℂ (Fin (k + 1)) := c • WithLp.toLp 2 w with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, hc, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hwn]
  have horth : Orthonormal ℂ (({Fin.last k} : Set (Fin (k + 1))).domRestrict (fun _ => u)) := by
    refine ⟨fun _ => hu1, fun i j hij => absurd ?_ hij⟩
    exact Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans (Set.mem_singleton_iff.1 j.2).symm)
  obtain ⟨bON, hbON⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : finrank ℂ (EuclideanSpace ℂ (Fin (k + 1))) = Fintype.card (Fin (k + 1))) horth
  have hb2 : bON (Fin.last k) = u := hbON (Fin.last k) (Set.mem_singleton _)
  set U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := of fun i j => (bON j).ofLp i with hU
  have hUU : Uᴴ * U = 1 := by
    ext j k
    have h := (orthonormal_iff_ite.1 bON.orthonormal) j k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    simp only [hU, conjTranspose_apply, Matrix.of_apply, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  set V : Matrix (Fin (k + 1)) (Fin k) ℂ := of fun i j => U i (Fin.castSucc j) with hV
  have hVV : V * Vᴴ = 1 - (c * star c) • vecMulVec w (star w) := by
    ext i l
    have h := congrFun (congrFun hUU' i) l
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at h
    simp only [conjTranspose_apply] at h
    have hlast : ∀ i, U i (Fin.last k) = c * w i := by
      intro i
      simp only [hU, of_apply]
      rw [hb2, hu]
      rfl
    rw [hlast, hlast] at h
    simp only [Matrix.mul_apply, conjTranspose_apply, hV, of_apply, Matrix.sub_apply,
      Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
    rw [← h, star_mul']
    ring
  have hK := mul_kron_eq_zero hk0 hk1
  set K : Mat 2 (k + 1) := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ vecMulVec w (star w) with hKdef
  have hKH : Kᴴ = K := by
    rw [hKdef, conjTranspose_kronecker, conjTranspose_one]
    congr 1
    ext i j
    simp [vecMulVec_apply, mul_comm]
  have hρH : ρᴴ = ρ := hρ.hermitian
  have hK' : K * ρ = 0 := by
    have := congrArg conjTranspose hK
    rwa [conjTranspose_mul, hKH, hρH, conjTranspose_zero] at this
  have hkron : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 - (c * star c) • vecMulVec w (star w)) =
      1 - (c * star c) • K := by
    ext ⟨a, k⟩ ⟨b, l⟩
    simp only [hKdef, kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply,
      smul_eq_mul, Prod.mk.injEq]
    split_ifs <;> simp_all
  have hback : lop (1 : Matrix (Fin 2) (Fin 2) ℂ) V (lop (1 : Matrix (Fin 2) (Fin 2) ℂ) Vᴴ ρ) = ρ := by
    rw [lop_lop, Matrix.one_mul, hVV, lop, hkron, conjTranspose_sub, conjTranspose_one,
      conjTranspose_smul, hKH]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hK, hK',
      smul_zero, sub_zero]
  exact ⟨V, hback⟩

/-- **If `(ρ₀₀ + ρ₁₁) w = 0` for some `w ≠ 0`, the PPT operator ρ is separable**: it lives on
`ℂ² ⊗ w^⊥ ≅ ℂ² ⊗ ℂ²`, where the two-qubit theorem applies. -/
theorem sep_of_corner_kernel {ρ : Mat 2 3} (hρ : IsPPT ρ) {w : Fin 3 → ℂ} (hw : w ≠ 0)
    (hk : (blkOf ρ 0 0 + blkOf ρ 1 1) *ᵥ w = 0) : IsSeparable ρ := by
  obtain ⟨V, hV⟩ := exists_compress hρ.1 hw hk
  rw [← hV]
  exact isSeparable_lop _ _ (pptSeparable22 _ (isPPT_lop _ Vᴴ hρ))

/-! ## Reduction 2: a shear makes the corner block invertible -/

theorem dotProduct_transpose_star (X : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) :
    w ⬝ᵥ (Xᵀ *ᵥ star w) = star w ⬝ᵥ (X *ᵥ w) := by
  simp only [dotProduct, mulVec, transpose_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem star_transpose_mulVec_star (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    star (Xᵀ *ᵥ star v) = Xᴴ *ᵥ v := by
  ext i
  simp only [Pi.star_apply, mulVec, dotProduct, transpose_apply, conjTranspose_apply, star_sum,
    star_mul', star_star]

theorem star_mulVec_dotProduct_of_hermitian {X : Matrix (Fin m) (Fin m) ℂ} (hX : Xᴴ = X)
    (v w : Fin m → ℂ) : star (X *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (X *ᵥ w) := by
  rw [star_mulVec, hX, ← dotProduct_mulVec]

/-- The blocks of a Hermitian block matrix. -/
theorem blk_hermitian {A B C : Matrix (Fin m) (Fin m) ℂ} (h : (blk A B Bᴴ C)ᴴ = blk A B Bᴴ C) :
    Aᴴ = A ∧ Cᴴ = C := by
  rw [blk_conjTranspose] at h
  exact ⟨by simpa using congrArg (blkOf · 0 0) h, by simpa using congrArg (blkOf · 1 1) h⟩

/-- **A shear that shrinks the corner kernel to that of `A + C`.** If `[[A, B], [Bᴴ, C]]` on `ℂ² ⊗ ℂᵐ`
is PPT, some real `z` makes every kernel vector of `A + z B + z Bᴴ + z² C` a kernel vector of `A + C`.
Otherwise there are vectors `w` with `(A + C) w ≠ 0` and `A w = z² C w` for `m + 1` distinct `z²`; these
are `C`-orthogonal with `C w ≠ 0`, so `m + 1` independent vectors in ℂᵐ. -/
theorem exists_shear_ker {A B C : Matrix (Fin m) (Fin m) ℂ} (hρ : IsPPT (blk A B Bᴴ C)) :
    ∃ z : ℝ, ∀ w : Fin m → ℂ,
      (A + star (z : ℂ) • B + (z : ℂ) • Bᴴ + ((z : ℂ) * star (z : ℂ)) • C) *ᵥ w = 0 → (A + C) *ᵥ w = 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨hAH, hCH⟩ := blk_hermitian hρ.1.hermitian
  have hCpsd : IsPSD C := by simpa using isPSD_blkOf_11 hρ.1
  -- a kernel vector of the sheared corner solves A w = z² C w
  have key : ∀ z : ℝ, ∀ w : Fin m → ℂ,
      (A + star (z : ℂ) • B + (z : ℂ) • Bᴴ + ((z : ℂ) * star (z : ℂ)) • C) *ᵥ w = 0 →
        A *ᵥ w = ((z : ℂ) * z) • (C *ᵥ w) := by
    intro z w hw
    have hzc : star (z : ℂ) = z := Complex.conj_ofReal z
    rw [hzc] at hw
    have e1 : star (bvec w ((z : ℂ) • w)) ⬝ᵥ (blk A B Bᴴ C *ᵥ bvec w ((z : ℂ) • w)) = 0 := by
      rw [blk_mulVec_bvec, star_bvec_dotProduct]
      have h0 : star w ⬝ᵥ ((A + (z : ℂ) • B + (z : ℂ) • Bᴴ + ((z : ℂ) * z) • C) *ᵥ w) = 0 := by
        rw [hw, dotProduct_zero]
      simp only [add_mulVec, smul_mulVec, mulVec_smul, dotProduct_add, dotProduct_smul, star_smul,
        smul_dotProduct, hzc, smul_eq_mul] at h0 ⊢
      linear_combination h0
    have h1 := isPSD_mulVec_eq_zero hρ.1 e1
    rw [blk_mulVec_bvec] at h1
    obtain ⟨h1a, -⟩ := bvec_eq_zero h1
    have e2 : star (bvec (star w) ((z : ℂ) • star w)) ⬝ᵥ
        (pt (blk A B Bᴴ C) *ᵥ bvec (star w) ((z : ℂ) • star w)) = 0 := by
      rw [pt_blk, blk_mulVec_bvec, star_bvec_dotProduct]
      have h0 : star w ⬝ᵥ ((A + (z : ℂ) • B + (z : ℂ) • Bᴴ + ((z : ℂ) * z) • C) *ᵥ w) = 0 := by
        rw [hw, dotProduct_zero]
      simp only [add_mulVec, smul_mulVec, mulVec_smul, dotProduct_add, dotProduct_smul, star_smul,
        smul_dotProduct, hzc, smul_eq_mul, star_star, dotProduct_transpose_star] at h0 ⊢
      linear_combination h0
    have h2 := isPSD_mulVec_eq_zero hρ.2 e2
    rw [pt_blk, blk_mulVec_bvec] at h2
    obtain ⟨-, h2b⟩ := bvec_eq_zero h2
    have h2b' : B *ᵥ w + (z : ℂ) • (C *ᵥ w) = 0 := by
      have := congrArg star h2b
      rwa [star_add, star_zero, mulVec_smul, star_smul, star_transpose_mulVec_star,
        star_transpose_mulVec_star, conjTranspose_conjTranspose, hCH, hzc] at this
    ext i
    have e1 := congrFun h1a i
    have e2 := congrFun h2b' i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul, Pi.zero_apply] at e1 e2 ⊢
    linear_combination e1 - (z : ℂ) * e2
  -- m + 1 values of z
  have hex : ∀ i : Fin (m + 1), ∃ w : Fin m → ℂ,
      (A + star (((i : ℕ) + 1 : ℝ) : ℂ) • B + (((i : ℕ) + 1 : ℝ) : ℂ) • Bᴴ +
        ((((i : ℕ) + 1 : ℝ) : ℂ) * star (((i : ℕ) + 1 : ℝ) : ℂ)) • C) *ᵥ w = 0 ∧ (A + C) *ᵥ w ≠ 0 :=
    fun i => hall _
  choose w hwk hw0 using hex
  set μ : Fin (m + 1) → ℂ := fun i => (((i : ℕ) + 1 : ℝ) : ℂ) * (((i : ℕ) + 1 : ℝ) : ℂ) with hμ
  have hA : ∀ i, A *ᵥ w i = μ i • (C *ᵥ w i) := fun i => key _ _ (hwk i)
  have hμreal : ∀ i, star (μ i) = μ i := fun i => by simp [hμ]
  have hμinj : ∀ i j, i ≠ j → μ j - μ i ≠ 0 := by
    intro i j hij h
    have h' : (((j : ℕ) + 1 : ℝ) * ((j : ℕ) + 1 : ℝ) : ℝ) = (((i : ℕ) + 1 : ℝ) * ((i : ℕ) + 1 : ℝ)) := by
      have := sub_eq_zero.1 h
      simp only [hμ] at this
      exact_mod_cast this
    have h'' : ((j : ℕ) + 1 : ℝ) = ((i : ℕ) + 1 : ℝ) := by
      have hi : (0 : ℝ) ≤ (i : ℕ) + 1 := by positivity
      have hj : (0 : ℝ) ≤ (j : ℕ) + 1 := by positivity
      nlinarith
    exact hij (Fin.ext (by exact_mod_cast (add_right_cancel h'').symm))
  have hCw : ∀ i, C *ᵥ w i ≠ 0 := by
    intro i h
    exact hw0 i (by rw [add_mulVec, hA i, h, smul_zero, zero_add])
  have horth : ∀ i j, i ≠ j → star (w i) ⬝ᵥ (C *ᵥ w j) = 0 := by
    intro i j hij
    have e1 : star (w i) ⬝ᵥ (A *ᵥ w j) = μ j * (star (w i) ⬝ᵥ (C *ᵥ w j)) := by
      rw [hA j, dotProduct_smul, smul_eq_mul]
    have e2 : star (w i) ⬝ᵥ (A *ᵥ w j) = μ i * (star (w i) ⬝ᵥ (C *ᵥ w j)) := by
      rw [← star_mulVec_dotProduct_of_hermitian hAH, hA i, star_smul, smul_dotProduct, hμreal,
        star_mulVec_dotProduct_of_hermitian hCH, smul_eq_mul]
    have : (μ j - μ i) * (star (w i) ⬝ᵥ (C *ᵥ w j)) = 0 := by linear_combination e2 - e1
    exact (mul_eq_zero.1 this).resolve_left (hμinj i j hij)
  have hpos : ∀ i, star (w i) ⬝ᵥ (C *ᵥ w i) ≠ 0 := fun i h =>
    hCw i (isPSD_mulVec_eq_zero hCpsd h)
  have hind : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun v => star (w j) ⬝ᵥ (C *ᵥ v)) hg
    simp only [mulVec_sum, dotProduct_sum, mulVec_smul, dotProduct_smul, smul_eq_mul, mulVec_zero,
      dotProduct_zero] at this
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at this
    exact (mul_eq_zero.1 this).resolve_right (hpos j)
  have := hind.fintype_card_le_finrank
  simp at this

/-- **A shear that makes the corner invertible**: if moreover `A + C` is invertible, some real `z` makes
`A + z B + z Bᴴ + z² C` invertible. -/
theorem exists_shear {A B C : Matrix (Fin m) (Fin m) ℂ} (hρ : IsPPT (blk A B Bᴴ C))
    (hAC : (A + C).det ≠ 0) :
    ∃ z : ℝ, (A + star (z : ℂ) • B + (z : ℂ) • Bᴴ + ((z : ℂ) * star (z : ℂ)) • C).det ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_shear_ker hρ
  refine ⟨z, fun h0 => ?_⟩
  obtain ⟨w, hw, hw0⟩ := exists_mulVec_eq_zero_iff.2 h0
  exact hAC (exists_mulVec_eq_zero_iff.1 ⟨w, hw, hz w hw0⟩)

/-! ## Every extreme ray of the PPT cone on ℂ² ⊗ ℂ³ is separable -/

theorem blkOf_10_of_hermitian {ρ : Mat 2 m} (h : ρᴴ = ρ) : blkOf ρ 1 0 = (blkOf ρ 0 1)ᴴ := by
  ext k l
  have := congrFun (congrFun h (1, k)) (0, l)
  simp only [conjTranspose_apply] at this
  simp only [blkOf, conjTranspose_apply]
  exact this.symm

theorem shear_mul_inv (z : ℂ) : !![(1 : ℂ), -z; 0, 1] * !![(1 : ℂ), z; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Every extreme ray of the PPT cone on `ℂ² ⊗ ℂ³` is separable.** -/
theorem sep_of_extreme {ρ : Mat 2 3} (hρ : IsExtremePPT ρ) : IsSeparable ρ := by
  have hH : ρᴴ = ρ := hρ.1.1.hermitian
  have h10 := blkOf_10_of_hermitian hH
  have hρblk : ρ = blk (blkOf ρ 0 0) (blkOf ρ 0 1) (blkOf ρ 0 1)ᴴ (blkOf ρ 1 1) := by
    rw [← h10]
    exact (blk_blkOf ρ).symm
  by_cases hAC : (blkOf ρ 0 0 + blkOf ρ 1 1).det = 0
  · obtain ⟨w, hw, hw0⟩ := exists_mulVec_eq_zero_iff.2 hAC
    exact sep_of_corner_kernel hρ.1 hw hw0
  · obtain ⟨z, hz⟩ := exists_shear (hρblk ▸ hρ.1) hAC
    set G : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), (z : ℂ); 0, 1] with hG
    have hGG : !![(1 : ℂ), -(z : ℂ); 0, 1] * G = 1 := shear_mul_inv _
    have h00 : blkOf (lop G (1 : Matrix (Fin 3) (Fin 3) ℂ) ρ) 0 0 = blkOf ρ 0 0 + star (z : ℂ) • blkOf ρ 0 1 +
        (z : ℂ) • (blkOf ρ 0 1)ᴴ + ((z : ℂ) * star (z : ℂ)) • blkOf ρ 1 1 := by
      rw [hG, blkOf_lop_shear, h10]
    have hpsd : IsPSD (blkOf (lop G (1 : Matrix (Fin 3) (Fin 3) ℂ) ρ) 0 0) := isPSD_blkOf_00 (isPSD_lop _ _ hρ.1.1)
    obtain ⟨F, hF⟩ := hpsd.gram
    have hFdet : IsUnit F.det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      apply hz
      rw [← h00, hF, det_mul, det_conjTranspose, h0, mul_zero]
    have hFHdet : IsUnit Fᴴ.det := by
      rw [det_conjTranspose]
      exact hFdet.star
    set M : Matrix (Fin 3) (Fin 3) ℂ := (Fᴴ)⁻¹ with hM
    have hMM : Fᴴ * M = 1 := mul_nonsing_inv _ hFHdet
    have hMM' : M * Fᴴ = 1 := nonsing_inv_mul _ hFHdet
    have hρ₂ : lop (1 : Matrix (Fin 2) (Fin 2) ℂ) M (lop G (1 : Matrix (Fin 3) (Fin 3) ℂ) ρ) = lop G M ρ := by rw [lop_lop, Matrix.one_mul, Matrix.mul_one]
    have h00' : blkOf (lop G M ρ) 0 0 = 1 := by
      rw [← hρ₂, blkOf_lop_one, hF]
      have hMH : Mᴴ = F⁻¹ := by rw [hM, conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
      rw [hMH, ← Matrix.mul_assoc, hMM', Matrix.one_mul, mul_nonsing_inv _ hFdet]
    have hext : IsExtremePPT (lop G M ρ) := isExtremePPT_lop hGG hMM hρ
    have hform : lop G M ρ = blk 1 (blkOf (lop G M ρ) 0 1) (blkOf (lop G M ρ) 0 1)ᴴ
        (blkOf (lop G M ρ) 1 1) := by
      rw [← h00', ← blkOf_10_of_hermitian hext.1.1.hermitian]
      exact (blk_blkOf _).symm
    have hsep₂ : IsSeparable (lop G M ρ) := by
      rw [hform] at hext ⊢
      exact sep_of_extreme_normalized hext
    have hback : lop !![(1 : ℂ), -(z : ℂ); 0, 1] Fᴴ (lop G M ρ) = ρ := by
      rw [lop_lop, hGG, hMM, lop_one]
    rw [← hback]
    exact isSeparable_lop _ _ hsep₂

/-! ## Krein–Milman: from extreme rays to all PPT operators -/

theorem retr_smul {n m : ℕ} (t : ℝ) (X : Mat n m) : retr (t • X) = t * retr X := by
  simp only [retr, Matrix.smul_apply, Complex.real_smul, ← Finset.mul_sum, Complex.re_ofReal_mul]

theorem eq_zero_of_retr {n m : ℕ} {P : Mat n m} (h : IsPSD P) (h0 : retr P = 0) : P = 0 := by
  ext x y
  have := h.norm_entry_le x y
  rw [h0, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- The PPT operators of trace one. -/
def pptSlice : Set (Mat 2 3) := {ρ | IsPPT ρ ∧ retr ρ = 1}

theorem convex_pptSlice : Convex ℝ pptSlice := by
  intro x hx y hy a b ha hb hab
  refine ⟨⟨(hx.1.1.smul ha).add (hy.1.1.smul hb), ?_⟩, ?_⟩
  · rw [pt_add, pt_smul, pt_smul]
    exact (hx.1.2.smul ha).add (hy.1.2.smul hb)
  · rw [retr_add, retr_smul, retr_smul, hx.2, hy.2, mul_one, mul_one, hab]

theorem isCompact_pptSlice : IsCompact pptSlice := by
  let box : Set (Mat 2 3) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 2
  have hbox : IsCompact box :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbox.of_isClosed_subset ?_ ?_
  · exact ((isClosed_psd.inter (isClosed_psd.preimage continuous_pt)).inter
      (isClosed_eq continuous_retr continuous_const))
  · rintro ρ ⟨hρ, htr⟩ x _ y _
    rw [Metric.mem_closedBall, dist_zero_right]
    have := hρ.1.norm_entry_le x y
    rw [htr] at this
    linarith

theorem isExtremePPT_of_mem_extremePoints {ρ : Mat 2 3} (h : ρ ∈ pptSlice.extremePoints ℝ) :
    IsExtremePPT ρ := by
  rw [mem_extremePoints] at h
  obtain ⟨⟨hρ, htr⟩, hext⟩ := h
  refine ⟨hρ, fun ρ₁ ρ₂ h₁ h₂ hsum => ?_⟩
  have t₁ := h₁.1.retr_nonneg
  have t₂ := h₂.1.retr_nonneg
  have htot : retr ρ₁ + retr ρ₂ = 1 := by rw [← retr_add, ← hsum, htr]
  by_cases ht1 : retr ρ₁ = 0
  · exact ⟨0, by rw [zero_smul]; exact eq_zero_of_retr h₁.1 ht1⟩
  by_cases ht2 : retr ρ₂ = 0
  · refine ⟨1, ?_⟩
    rw [one_smul, hsum, eq_zero_of_retr h₂.1 ht2, add_zero]
  have hp1 : 0 < retr ρ₁ := lt_of_le_of_ne t₁ (Ne.symm ht1)
  have hp2 : 0 < retr ρ₂ := lt_of_le_of_ne t₂ (Ne.symm ht2)
  have hm1 : (retr ρ₁)⁻¹ • ρ₁ ∈ pptSlice :=
    ⟨isPPT_smul h₁ (inv_nonneg.2 t₁), by rw [retr_smul, inv_mul_cancel₀ ht1]⟩
  have hm2 : (retr ρ₂)⁻¹ • ρ₂ ∈ pptSlice :=
    ⟨isPPT_smul h₂ (inv_nonneg.2 t₂), by rw [retr_smul, inv_mul_cancel₀ ht2]⟩
  have hseg : ρ ∈ openSegment ℝ ((retr ρ₁)⁻¹ • ρ₁) ((retr ρ₂)⁻¹ • ρ₂) :=
    ⟨retr ρ₁, retr ρ₂, hp1, hp2, htot, by
      rw [smul_smul, smul_smul, mul_inv_cancel₀ ht1, mul_inv_cancel₀ ht2, one_smul, one_smul, hsum]⟩
  obtain ⟨h1, -⟩ := hext _ hm1 _ hm2 hseg
  refine ⟨retr ρ₁, ?_⟩
  rw [← h1, smul_smul, mul_inv_cancel₀ ht1, one_smul]

theorem pair_smul_left {n m : ℕ} (t : ℝ) (ρ X : Mat n m) : pair (t • ρ) X = t * pair ρ X := by
  simp only [pair, Matrix.smul_apply, Complex.real_smul, Finset.mul_sum, mul_assoc]

theorem continuous_pair_left {n m : ℕ} (X : Mat n m) : Continuous fun ρ : Mat n m => pair ρ X := by
  unfold pair
  fun_prop

/-- **Every PPT operator on `ℂ² ⊗ ℂ³` pairs nonnegatively with the Choi matrix of every positive map
`M₂ → M₃`.** The trace-one PPT operators form a compact convex set; by Krein–Milman it is the closed
convex hull of its extreme points, which are separable (`sep_of_extreme`). -/
theorem ppt_pairing_nonneg {ρ : Mat 2 3} (hρ : IsPPT ρ)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ} (hΦ : IsPositive Φ) :
    0 ≤ (pair ρ (choi Φ)).re := by
  set T : Set (Mat 2 3) := {σ | 0 ≤ (pair σ (choi Φ)).re} with hTdef
  have hT : IsClosed T :=
    isClosed_le continuous_const (Complex.continuous_re.comp (continuous_pair_left _))
  have hTc : Convex ℝ T := by
    intro x hx y hy a b ha hb _
    show 0 ≤ (pair (a • x + b • y) (choi Φ)).re
    rw [pair_add, pair_smul_left, pair_smul_left, Complex.add_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hext : pptSlice.extremePoints ℝ ⊆ T := fun σ hσ =>
    pair_choi_nonneg_of_separable (sep_of_extreme (isExtremePPT_of_mem_extremePoints hσ)) hΦ
  have hK : pptSlice ⊆ T := by
    rw [← closure_convexHull_extremePoints isCompact_pptSlice convex_pptSlice]
    exact closure_minimal (convexHull_min hext hTc) hT
  by_cases h0 : retr ρ = 0
  · rw [eq_zero_of_retr hρ.1 h0]
    simp [pair]
  · have hpos : 0 < retr ρ := lt_of_le_of_ne hρ.1.retr_nonneg (Ne.symm h0)
    have hmem : (retr ρ)⁻¹ • ρ ∈ pptSlice :=
      ⟨isPPT_smul hρ (inv_nonneg.2 hpos.le), by rw [retr_smul, inv_mul_cancel₀ h0]⟩
    have h1 : 0 ≤ (pair ((retr ρ)⁻¹ • ρ) (choi Φ)).re := hK hmem
    rw [pair_smul_left, Complex.re_ofReal_mul] at h1
    exact nonneg_of_mul_nonneg_right (by linarith) (inv_pos.2 hpos)

/-! ## Woronowicz's theorem and the read cap -/

/-- **Woronowicz's theorem**: every positive linear map `M₂(ℂ) → M₃(ℂ)` is decomposable. -/
theorem woronowicz : AllDecomposable 2 3 :=
  allDecomposable_of_pptPairing fun _ hρ _ hΦ => ppt_pairing_nonneg hρ hΦ

/-- **The (2,3) type is readable**, with no hypothesis. -/
theorem readable_two_three : Readable 2 3 :=
  readable_iff_allDecomposable.2 woronowicz

/-- **The alpha Letter's read cap holds** for its own readability, with no hypothesis: a link type
`(d₁, d₂)` with `d₁, d₂ ≥ 2` is readable exactly when `d₁ d₂ ≤ 6`. -/
theorem readcap : ReadCap Readable :=
  readcap_of_woronowicz woronowicz

end ChainWoronowicz

end

end -- public section

#print axioms ChainWoronowicz.sep_of_extreme
#print axioms ChainWoronowicz.woronowicz
#print axioms ChainWoronowicz.readable_two_three
#print axioms ChainWoronowicz.readcap
