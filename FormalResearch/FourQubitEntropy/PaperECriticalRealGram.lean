import FormalResearch.FourQubitEntropy.PaperECriticalGram

/-!
# Simultaneous real singular values (`lem:fqe-real-gram`), square case

For a complex square matrix `Z` (indexed by a finite type), `Z Zᴴ` and `Zᴴ Z` are real matrices if and
only if `Z = O₁ diag(v) O₂ᵀ` with `O₁, O₂` real orthogonal and `v` complex. Paper E states the lemma for
`m × n` matrices; only the square case (`m = n = 4`) is used for the critical normal form and only the
square case is formalised here.

Proof (different from the paper's SVD argument, avoiding a real SVD): with `Z = X + iY`, the conditions
are `X Yᵀ = Y Xᵀ`, `Xᵀ Y = Yᵀ X`, so `XᵀX`, `YᵀY`, `XᵀY` are commuting real symmetric matrices; one
real orthogonal `Q` diagonalises all of them, the columns `w_k` of `Z Q` are pairwise orthogonal for the
Hermitian and the bilinear form, and reality of `Z Zᴴ` forces each column to be a complex multiple of a
real vector; the real vectors are completed to a real orthonormal basis.

All statements are proved (no hypotheses, no `native_decide`).
-/

open scoped Matrix ComplexConjugate

namespace FormalResearch.FourQubitEntropy.PaperECritical

variable {ι : Type*} [Fintype ι]

theorem im_mul_conjTranspose (Z : Matrix ι ι ℂ) (i j : ι) :
    ((Z * Zᴴ) i j).im =
      ((Z.map Complex.im * (Z.map Complex.re)ᵀ - Z.map Complex.re * (Z.map Complex.im)ᵀ) i j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum, Matrix.sub_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem im_conjTranspose_mul (Z : Matrix ι ι ℂ) (i j : ι) :
    ((Zᴴ * Z) i j).im =
      (((Z.map Complex.re)ᵀ * Z.map Complex.im - (Z.map Complex.im)ᵀ * Z.map Complex.re) i j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum, Matrix.sub_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Column lemma: a complex vector `c` with `c i * s = conj (c i) * δ` (`s = ‖c‖²`) is a complex
multiple of a real unit vector (or zero). -/
theorem column_lemma (c : ι → ℂ) (δ : ℂ)
    (hkey : ∀ i, c i * ((∑ j, Complex.normSq (c j) : ℝ) : ℂ) = (starRingEnd ℂ) (c i) * δ) :
    ∃ (v : ℂ) (e : ι → ℝ), (∀ i, c i = (e i : ℂ) * v) ∧
      (c ≠ 0 → v ≠ 0 ∧ ∑ i, e i ^ 2 = 1) := by
  by_cases hc : c = 0
  · exact ⟨0, 0, fun i => by simp [hc], fun h => (h hc).elim⟩
  set s : ℝ := ∑ j, Complex.normSq (c j) with hs
  obtain ⟨i0, hi0⟩ : ∃ i0, c i0 ≠ 0 := by
    by_contra h; push Not at h; exact hc (funext h)
  have hspos : 0 < s := by
    have h1 : 0 < Complex.normSq (c i0) := Complex.normSq_pos.2 hi0
    have h2 : Complex.normSq (c i0) ≤ s :=
      Finset.single_le_sum (f := fun j => Complex.normSq (c j)) (fun j _ => Complex.normSq_nonneg _)
        (Finset.mem_univ i0)
    linarith
  -- |δ| = s
  have hδ : ‖δ‖ = s := by
    have h := congrArg norm (hkey i0)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg hspos.le] at h
    have hn : 0 < ‖c i0‖ := norm_pos_iff.2 hi0
    have := mul_left_cancel₀ hn.ne' h
    exact this.symm
  set l : ℂ := δ / (s : ℂ) with hl
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hlnorm : ‖l‖ = 1 := by
    rw [hl, norm_div, hδ, Complex.norm_real, Real.norm_of_nonneg hspos.le, div_self hspos.ne']
  have hcl : ∀ i, c i = l * (starRingEnd ℂ) (c i) := by
    intro i
    have := hkey i
    rw [hl]; field_simp
    linear_combination this
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq l (show 0 < 2 by norm_num)
  have hμn : ‖μ‖ = 1 := by
    have : ‖μ‖ ^ 2 = 1 := by rw [← norm_pow, hμ, hlnorm]
    nlinarith [norm_nonneg μ]
  have hμc : (starRingEnd ℂ) μ * μ = 1 := by
    rw [Complex.conj_mul', hμn]; simp
  have hreal : ∀ i, (starRingEnd ℂ) ((starRingEnd ℂ) μ * c i) = (starRingEnd ℂ) μ * c i := by
    intro i
    have h1 := hcl i
    have : (starRingEnd ℂ) μ * c i = μ * (starRingEnd ℂ) (c i) := by
      calc (starRingEnd ℂ) μ * c i = (starRingEnd ℂ) μ * (l * (starRingEnd ℂ) (c i)) := by rw [← h1]
        _ = ((starRingEnd ℂ) μ * μ) * (μ * (starRingEnd ℂ) (c i)) := by rw [← hμ]; ring
        _ = μ * (starRingEnd ℂ) (c i) := by rw [hμc]; ring
    rw [this]; simpa using this
  set r : ι → ℝ := fun i => ((starRingEnd ℂ) μ * c i).re with hr
  have hrc : ∀ i, c i = μ * (r i : ℂ) := by
    intro i
    have h1 : (starRingEnd ℂ) μ * c i = (r i : ℂ) := by
      apply Complex.ext
      · simp [hr]
      · have := Complex.conj_eq_iff_im.1 (hreal i); simp [hr, this]
    calc c i = (μ * (starRingEnd ℂ) μ) * c i := by
          rw [mul_comm μ, hμc, one_mul]
      _ = μ * ((starRingEnd ℂ) μ * c i) := by ring
      _ = μ * (r i : ℂ) := by rw [h1]
  have hsum : ∑ i, r i ^ 2 = s := by
    rw [hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrc i, Complex.normSq_mul, Complex.normSq_ofReal]
    have : Complex.normSq μ = 1 := by rw [Complex.normSq_eq_norm_sq, hμn]; norm_num
    rw [this]; ring
  refine ⟨μ * (Real.sqrt s : ℂ), fun i => (r i / Real.sqrt s), ?_, fun _ => ⟨?_, ?_⟩⟩
  · intro i
    rw [hrc i]
    have : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hspos).ne'
    push_cast
    field_simp
  · have : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hspos).ne'
    exact mul_ne_zero (by intro h; rw [h] at hμn; simp at hμn) this
  · simp only [div_pow]
    rw [← Finset.sum_div, hsum, Real.sq_sqrt hspos.le, div_self hspos.ne']
variable [DecidableEq ι]

/-- `ofReal` on matrices as a ring homomorphism. -/
noncomputable abbrev rc : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix

theorem rc_apply (M : Matrix ι ι ℝ) (i j : ι) : rc M i j = (M i j : ℂ) := rfl

theorem rc_conjTranspose (M : Matrix ι ι ℝ) : (rc M)ᴴ = rc Mᵀ := by
  ext i j; simp [rc_apply, Matrix.conjTranspose_apply]

theorem rc_transpose (M : Matrix ι ι ℝ) : (rc M)ᵀ = rc Mᵀ := by
  ext i j; simp [rc_apply]

theorem decomp (Z : Matrix ι ι ℂ) :
    Z = rc (Z.map Complex.re) + Complex.I • rc (Z.map Complex.im) := by
  ext i j
  apply Complex.ext <;> simp [rc_apply]

theorem gram1 (X Y : Matrix ι ι ℝ) (P2 : Xᵀ * Y = Yᵀ * X) :
    (rc X + Complex.I • rc Y)ᴴ * (rc X + Complex.I • rc Y) = rc (Xᵀ * X + Yᵀ * Y) := by
  have hP : rc Xᵀ * rc Y = rc Yᵀ * rc X := by rw [← map_mul, ← map_mul, P2]
  have e1 : (rc X + Complex.I • rc Y)ᴴ = rc Xᵀ - Complex.I • rc Yᵀ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, rc_conjTranspose, rc_conjTranspose]
    simp [sub_eq_add_neg]
  rw [map_add, map_mul, map_mul, e1]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul, hP,
    Complex.I_mul_I]
  module

theorem gram2 (X Y : Matrix ι ι ℝ) (P2 : Xᵀ * Y = Yᵀ * X) :
    (rc X + Complex.I • rc Y)ᵀ * (rc X + Complex.I • rc Y) =
      rc (Xᵀ * X - Yᵀ * Y) + Complex.I • rc (Xᵀ * Y + Xᵀ * Y) := by
  have hP : rc Xᵀ * rc Y = rc Yᵀ * rc X := by rw [← map_mul, ← map_mul, P2]
  have e1 : (rc X + Complex.I • rc Y)ᵀ = rc Xᵀ + Complex.I • rc Yᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, rc_transpose, rc_transpose]
  rw [map_sub, map_add, map_mul, map_mul, map_mul, e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
    ← hP, Complex.I_mul_I]
  match_scalars
  all_goals (ring_nf; try simp only [Complex.I_sq]; try ring_nf)

/-- Real orthogonal matrices (`Oᵀ O = 1`) are also `O Oᵀ = 1`. -/
theorem orth_mul_transpose {O : Matrix ι ι ℝ} (h : Oᵀ * O = 1) : O * Oᵀ = 1 :=
  mul_eq_one_comm.mp h

theorem real_gram_square (Z : Matrix ι ι ℂ)
    (h1 : ∀ i j, ((Z * Zᴴ) i j).im = 0) (h2 : ∀ i j, ((Zᴴ * Z) i j).im = 0) :
    ∃ (O₁ O₂ : Matrix ι ι ℝ) (v : ι → ℂ), O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧
      Z = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ := by
  classical
  obtain ⟨X, Y, hZ⟩ : ∃ X Y : Matrix ι ι ℝ, Z = rc X + Complex.I • rc Y :=
    ⟨Z.map Complex.re, Z.map Complex.im, decomp Z⟩
  have hX : Z.map Complex.re = X := by rw [hZ]; ext i j; simp [rc_apply]
  have hY : Z.map Complex.im = Y := by rw [hZ]; ext i j; simp [rc_apply]
  have P1 : X * Yᵀ = Y * Xᵀ := by
    ext i j
    have := h1 i j
    rw [im_mul_conjTranspose, hX, hY] at this
    simp only [Matrix.sub_apply] at this
    linarith
  have P2 : Xᵀ * Y = Yᵀ * X := by
    ext i j
    have := h2 i j
    rw [im_conjTranspose_mul, hX, hY] at this
    simp only [Matrix.sub_apply] at this
    linarith
  have hA : (Xᵀ * X)ᵀ = Xᵀ * X := by simp [Matrix.transpose_mul]
  have hB : (Yᵀ * Y)ᵀ = Yᵀ * Y := by simp [Matrix.transpose_mul]
  have hC : (Xᵀ * Y)ᵀ = Xᵀ * Y := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact P2.symm
  have cAC : Xᵀ * X * (Xᵀ * Y) = Xᵀ * Y * (Xᵀ * X) := by
    calc Xᵀ * X * (Xᵀ * Y) = Xᵀ * X * (Yᵀ * X) := by rw [P2]
      _ = Xᵀ * (X * Yᵀ) * X := by simp only [Matrix.mul_assoc]
      _ = Xᵀ * (Y * Xᵀ) * X := by rw [P1]
      _ = Xᵀ * Y * (Xᵀ * X) := by simp only [Matrix.mul_assoc]
  have cBC : Yᵀ * Y * (Xᵀ * Y) = Xᵀ * Y * (Yᵀ * Y) := by
    calc Yᵀ * Y * (Xᵀ * Y) = Yᵀ * (Y * Xᵀ) * Y := by simp only [Matrix.mul_assoc]
      _ = Yᵀ * (X * Yᵀ) * Y := by rw [P1]
      _ = (Yᵀ * X) * (Yᵀ * Y) := by simp only [Matrix.mul_assoc]
      _ = Xᵀ * Y * (Yᵀ * Y) := by rw [← P2]
  have cAB : Xᵀ * X * (Yᵀ * Y) = Yᵀ * Y * (Xᵀ * X) := by
    calc Xᵀ * X * (Yᵀ * Y) = Xᵀ * (X * Yᵀ) * Y := by simp only [Matrix.mul_assoc]
      _ = Xᵀ * (Y * Xᵀ) * Y := by rw [P1]
      _ = (Xᵀ * Y) * (Xᵀ * Y) := by simp only [Matrix.mul_assoc]
      _ = (Yᵀ * X) * (Yᵀ * X) := by rw [P2]
      _ = Yᵀ * (X * Yᵀ) * X := by simp only [Matrix.mul_assoc]
      _ = Yᵀ * (Y * Xᵀ) * X := by rw [P1]
      _ = Yᵀ * Y * (Xᵀ * X) := by simp only [Matrix.mul_assoc]
  obtain ⟨Q, hQ, hd⟩ := exists_orthogonal_simul_diag ![Xᵀ * X, Yᵀ * Y, Xᵀ * Y]
    (fun i => by fin_cases i; exacts [hA, hB, hC]) (fun i j => by
      fin_cases i <;> fin_cases j
      exacts [rfl, cAB, cAC, cAB.symm, rfl, cBC, cAC.symm, cBC.symm, rfl])
  obtain ⟨da, hda⟩ := hd 0
  obtain ⟨db, hdb⟩ := hd 1
  obtain ⟨dc, hdc⟩ := hd 2
  have hda' : Xᵀ * X * Q = Q * Matrix.diagonal da := hda
  have hdb' : Yᵀ * Y * Q = Q * Matrix.diagonal db := hdb
  have hdc' : Xᵀ * Y * Q = Q * Matrix.diagonal dc := hdc
  have hQ' : Q * Qᵀ = 1 := orth_mul_transpose hQ
  have hD : ∀ (M : Matrix ι ι ℝ) (d : ι → ℝ), M * Q = Q * Matrix.diagonal d →
      Qᵀ * M * Q = Matrix.diagonal d := fun M d h => by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hZZ1 : Zᴴ * Z = rc (Xᵀ * X + Yᵀ * Y) := by rw [← gram1 X Y P2, ← hZ]
  have hZZ2 : Zᵀ * Z = rc (Xᵀ * X - Yᵀ * Y) + Complex.I • rc (Xᵀ * Y + Xᵀ * Y) := by
    rw [← gram2 X Y P2, ← hZ]
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix ι ι ℂ, W = Z * rc Q := ⟨_, rfl⟩
  have hW1 : Wᴴ * W = rc (Matrix.diagonal (da + db)) := by
    rw [hWdef, Matrix.conjTranspose_mul, rc_conjTranspose]
    calc rc Qᵀ * Zᴴ * (Z * rc Q) = rc Qᵀ * (Zᴴ * Z) * rc Q := by simp only [Matrix.mul_assoc]
      _ = rc (Qᵀ * (Xᵀ * X + Yᵀ * Y) * Q) := by rw [hZZ1, map_mul, map_mul]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.add_mul, hD _ _ hda', hD _ _ hdb', Matrix.diagonal_add]
        rfl
  have hW2 : Wᵀ * W = rc (Matrix.diagonal (da - db)) + Complex.I • rc (Matrix.diagonal (dc + dc)) := by
    rw [hWdef, Matrix.transpose_mul, rc_transpose]
    calc rc Qᵀ * Zᵀ * (Z * rc Q) = rc Qᵀ * (Zᵀ * Z) * rc Q := by simp only [Matrix.mul_assoc]
      _ = rc (Qᵀ * (Xᵀ * X - Yᵀ * Y) * Q) + Complex.I • rc (Qᵀ * (Xᵀ * Y + Xᵀ * Y) * Q) := by
        rw [hZZ2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [map_mul]
      _ = _ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, hD _ _ hda', hD _ _ hdb',
          hD _ _ hdc', Matrix.diagonal_sub, Matrix.diagonal_add]
        rfl
  have hF1 : ∀ k l, k ≠ l → (Wᴴ * W) k l = 0 := fun k l hkl => by
    rw [hW1]; simp [rc_apply, Matrix.diagonal_apply_ne _ hkl]
  have hF2 : ∀ k l, k ≠ l → (Wᵀ * W) k l = 0 := fun k l hkl => by
    rw [hW2]; simp [rc_apply, Matrix.diagonal_apply_ne _ hkl]
  -- reality of `Z Zᴴ` gives the key relation between the columns of `W`
  have hQc2 : rc Q * (rc Q)ᴴ = 1 := by rw [rc_conjTranspose, ← map_mul, hQ', map_one]
  have hK : W * Wᴴ = Z * Zᴴ := by
    rw [hWdef, Matrix.conjTranspose_mul]
    calc Z * rc Q * ((rc Q)ᴴ * Zᴴ) = Z * (rc Q * (rc Q)ᴴ) * Zᴴ := by simp only [Matrix.mul_assoc]
      _ = Z * Zᴴ := by rw [hQc2, Matrix.mul_one]
  have hKreal : (Z * Zᴴ).map star = Z * Zᴴ := by
    ext i j
    exact Complex.conj_eq_iff_im.2 (h1 i j)
  have hmap : (W * Wᴴ).map star = W.map star * Wᵀ := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
  have hkeyM : W * (Wᴴ * W) = W.map star * (Wᵀ * W) := by
    have e1 : W * (Wᴴ * W) = (W * Wᴴ) * W := by rw [Matrix.mul_assoc]
    have e2 : W.map star * (Wᵀ * W) = (W.map star * Wᵀ) * W := by rw [Matrix.mul_assoc]
    rw [e1, e2, ← hmap, hK, hKreal]
  have hentry : ∀ i k, W i k * (Wᴴ * W) k k = (starRingEnd ℂ) (W i k) * (Wᵀ * W) k k := by
    intro i k
    have h := congrFun (congrFun hkeyM i) k
    have e1 : (W * (Wᴴ * W)) i k = W i k * (Wᴴ * W) k k := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single k (fun m _ hm => ?_) (fun h => absurd (Finset.mem_univ k) h)
      rw [hF1 m k hm, mul_zero]
    have e2 : (W.map star * (Wᵀ * W)) i k = (starRingEnd ℂ) (W i k) * (Wᵀ * W) k k := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single k (fun m _ hm => ?_) (fun h => absurd (Finset.mem_univ k) h)
      rw [hF2 m k hm, mul_zero]
    rw [← e1, ← e2]; exact h
  have hnorm : ∀ k, (Wᴴ * W) k k = ((∑ j, Complex.normSq (W j k) : ℝ) : ℂ) := by
    intro k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum,
      Complex.normSq_eq_conj_mul_self]
    rfl
  have hcol : ∀ k, ∃ (v : ℂ) (e : ι → ℝ), (∀ i, W i k = (e i : ℂ) * v) ∧
      ((fun i => W i k) ≠ 0 → v ≠ 0 ∧ ∑ i, e i ^ 2 = 1) := fun k =>
    column_lemma (fun i => W i k) ((Wᵀ * W) k k) (fun i => by
      rw [← hnorm k]; exact hentry i k)
  choose v e hve using hcol
  let S : Set ι := {k | (fun i => W i k) ≠ 0}
  let f : ι → EuclideanSpace ℝ ι := fun k => WithLp.toLp 2 (e k)
  have hon : Orthonormal ℝ (S.domRestrict f) := by
    rw [orthonormal_iff_ite]
    intro k l
    simp only [Set.domRestrict_apply, EuclideanSpace.inner_eq_star_dotProduct, f]
    by_cases hkl : k = l
    · subst hkl
      simp only [↓reduceIte, star_trivial, dotProduct]
      have := (hve k).2 k.2
      rw [← this.2]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have hne : (k : ι) ≠ l := fun h => hkl (Subtype.ext h)
      simp only [hkl, ↓reduceIte]
      have h0 := hF1 k l hne
      have hvk := ((hve k).2 k.2).1
      have hvl := ((hve l).2 l.2).1
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h0
      have h3 : ∀ i, (starRingEnd ℂ) (W i k) * W i l =
          ((starRingEnd ℂ) (v k) * v l) * ((e k i * e l i : ℝ) : ℂ) := fun i => by
        simp only [(hve k).1 i, (hve l).1 i, map_mul, Complex.conj_ofReal]; push_cast; ring
      have h4 : ((starRingEnd ℂ) (v k) * v l) * ((∑ i, e k i * e l i : ℝ) : ℂ) = 0 := by
        rw [← h0, Complex.ofReal_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (h3 i).symm
      have h5 : ((starRingEnd ℂ) (v k) * v l) ≠ 0 :=
        mul_ne_zero (by simpa using hvk) hvl
      have h6 := (mul_eq_zero.1 h4).resolve_left h5
      have h7 : (∑ i, e k i * e l i : ℝ) = 0 := by exact_mod_cast h6
      simp only [dotProduct, Pi.star_apply, star_trivial]
      rw [← h7]
      exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)) hon
  classical
  let v' : ι → ℂ := fun k => if k ∈ S then v k else 0
  have hWO : W = rc (Matrix.of fun i k => b k i) * Matrix.diagonal v' := by
    ext i k
    rw [Matrix.mul_diagonal]
    by_cases hk : k ∈ S
    · have hbk : b k = f k := hb k hk
      have : (b k) i = e k i := by rw [hbk]
      simp only [v', hk, ↓reduceIte, rc_apply, Matrix.of_apply, this]
      exact (hve k).1 i
    · have h0 : (fun i => W i k) = 0 := by
        by_contra h; exact hk h
      simp only [v', hk, ↓reduceIte, mul_zero]
      exact congrFun h0 i
  refine ⟨Matrix.of fun i k => b k i, Q, v', basisMatrix_orth b, hQ, ?_⟩
  rw [← hWO, hWdef, rc_transpose, Matrix.mul_assoc, ← map_mul, hQ', map_one, Matrix.mul_one]

theorem rc_diagonal (d : ι → ℝ) :
    rc (Matrix.diagonal d) = Matrix.diagonal (fun k => (d k : ℂ)) := by
  ext i j; by_cases h : i = j <;> simp [rc_apply, Matrix.diagonal_apply, h]

/-- Converse of `real_gram_square`: the Gram matrices of `O₁ diag(v) O₂ᵀ` are real. -/
theorem real_gram_of_normal_form (O₁ O₂ : Matrix ι ι ℝ) (v : ι → ℂ) (h1 : O₁ᵀ * O₁ = 1)
    (h2 : O₂ᵀ * O₂ = 1) :
    (∀ i j, (((rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) * (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ)ᴴ)
        i j).im = 0) ∧
    (∀ i j, ((((rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ)ᴴ * (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ))
        i j).im = 0)) := by
  have hD : Matrix.diagonal v * (Matrix.diagonal v)ᴴ =
      rc (Matrix.diagonal (fun k => Complex.normSq (v k))) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, rc_diagonal]
    congr 1; ext k; simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hD' : (Matrix.diagonal v)ᴴ * Matrix.diagonal v =
      rc (Matrix.diagonal (fun k => Complex.normSq (v k))) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, rc_diagonal]
    congr 1; ext k; simp [Complex.conj_mul', Complex.normSq_eq_norm_sq]
  have hO2 : (rc O₂)ᵀ * ((rc O₂)ᵀ)ᴴ = 1 := by
    rw [rc_transpose, rc_conjTranspose, Matrix.transpose_transpose, ← map_mul, h2, map_one]
  have hO1 : (rc O₁)ᴴ * rc O₁ = 1 := by
    rw [rc_conjTranspose, ← map_mul, h1, map_one]
  have hO2' : ((rc O₂)ᵀ)ᴴ * (rc O₂)ᵀ = 1 := by
    rw [rc_transpose, rc_conjTranspose, Matrix.transpose_transpose, ← map_mul, orth_mul_transpose h2, map_one]
  constructor
  · intro i j
    have e : (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) * (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ)ᴴ =
        rc (O₁ * Matrix.diagonal (fun k => Complex.normSq (v k)) * O₁ᵀ) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, map_mul, map_mul, ← rc_conjTranspose, ← hD]
      calc rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ * (((rc O₂)ᵀ)ᴴ * ((Matrix.diagonal v)ᴴ * (rc O₁)ᴴ))
          = rc O₁ * Matrix.diagonal v * ((rc O₂)ᵀ * ((rc O₂)ᵀ)ᴴ) * ((Matrix.diagonal v)ᴴ * (rc O₁)ᴴ) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hO2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e]; simp [rc_apply]
  · intro i j
    have e : (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ)ᴴ * (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) =
        rc (O₂ * Matrix.diagonal (fun k => Complex.normSq (v k)) * O₂ᵀ) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, map_mul, map_mul, ← rc_transpose, ← hD']
      have hT : ((rc O₂)ᵀ)ᴴ = rc O₂ := by
        rw [rc_transpose, rc_conjTranspose, Matrix.transpose_transpose]
      rw [hT]
      calc rc O₂ * ((Matrix.diagonal v)ᴴ * (rc O₁)ᴴ) * (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ)
          = rc O₂ * (Matrix.diagonal v)ᴴ * ((rc O₁)ᴴ * rc O₁) * Matrix.diagonal v * (rc O₂)ᵀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hO1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e]; simp [rc_apply]


theorem det_orth {O : Matrix ι ι ℝ} (h : Oᵀ * O = 1) : O.det = 1 ∨ O.det = -1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  exact mul_self_eq_one_iff.1 this

/-- The sign function `-1` at `i₀`, `1` elsewhere. -/
def sgn (i₀ : ι) (k : ι) : ℝ := if k = i₀ then -1 else 1

theorem sgn_mul_self (i₀ k : ι) : sgn i₀ k * sgn i₀ k = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem det_flip (i₀ : ι) : (Matrix.diagonal (sgn i₀)).det = -1 := by
  rw [Matrix.det_diagonal]
  simp [sgn]

theorem flipD (i₀ : ι) (v : ι → ℂ) :
    Matrix.diagonal (fun k => (sgn i₀ k : ℂ)) * Matrix.diagonal (fun k => (sgn i₀ k : ℂ) * v k) =
      Matrix.diagonal v := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; ext k
  have := sgn_mul_self i₀ k
  have h2 : (sgn i₀ k : ℂ) * (sgn i₀ k : ℂ) = 1 := by exact_mod_cast this
  rw [← mul_assoc, h2, one_mul]

theorem flipD' (i₀ : ι) (v : ι → ℂ) :
    Matrix.diagonal (fun k => (sgn i₀ k : ℂ) * v k) * Matrix.diagonal (fun k => (sgn i₀ k : ℂ)) =
      Matrix.diagonal v := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; ext k
  have := sgn_mul_self i₀ k
  have h2 : (sgn i₀ k : ℂ) * (sgn i₀ k : ℂ) = 1 := by exact_mod_cast this
  rw [mul_comm (sgn i₀ k : ℂ) (v k), mul_assoc, h2, mul_one]

theorem flipL (i₀ : ι) (O₁ O₂ : Matrix ι ι ℝ) (v : ι → ℂ)
    (Z : Matrix ι ι ℂ) (hZ : Z = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) :
    Z = rc (O₁ * Matrix.diagonal (sgn i₀)) * Matrix.diagonal (fun k => (sgn i₀ k : ℂ) * v k)
      * (rc O₂)ᵀ := by
  rw [hZ, map_mul, rc_diagonal]
  calc rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ
      = rc O₁ * (Matrix.diagonal (fun k => (sgn i₀ k : ℂ)) *
          Matrix.diagonal (fun k => (sgn i₀ k : ℂ) * v k)) * (rc O₂)ᵀ := by rw [flipD]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem flipR (i₀ : ι) (O₁ O₂ : Matrix ι ι ℝ) (v : ι → ℂ)
    (Z : Matrix ι ι ℂ) (hZ : Z = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) :
    Z = rc O₁ * Matrix.diagonal (fun k => (sgn i₀ k : ℂ) * v k) *
      (rc (O₂ * Matrix.diagonal (sgn i₀)))ᵀ := by
  rw [hZ, map_mul, rc_diagonal, Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ
      = rc O₁ * (Matrix.diagonal (fun k => (sgn i₀ k : ℂ) * v k) *
          Matrix.diagonal (fun k => (sgn i₀ k : ℂ))) * (rc O₂)ᵀ := by rw [flipD']
    _ = _ := by simp only [Matrix.mul_assoc]

/-- `lem:fqe-real-gram`, square case, with both orthogonal factors of determinant `1`. -/
theorem real_gram_square_SO (i₀ : ι) (Z : Matrix ι ι ℂ)
    (h1 : ∀ i j, ((Z * Zᴴ) i j).im = 0) (h2 : ∀ i j, ((Zᴴ * Z) i j).im = 0) :
    ∃ (O₁ O₂ : Matrix ι ι ℝ) (v : ι → ℂ), O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧ O₁.det = 1 ∧
      O₂.det = 1 ∧ Z = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ := by
  obtain ⟨O₁, O₂, v, hO₁, hO₂, hZ⟩ := real_gram_square Z h1 h2
  have hE : (Matrix.diagonal (sgn i₀))ᵀ * Matrix.diagonal (sgn i₀) = 1 := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; exact sgn_mul_self i₀ k
  have hdet : ∀ O : Matrix ι ι ℝ, Oᵀ * O = 1 → ∃ O' : Matrix ι ι ℝ, O'ᵀ * O' = 1 ∧ O'.det = 1 ∧
      (O' = O ∨ O' = O * Matrix.diagonal (sgn i₀)) := by
    intro O hO
    rcases det_orth hO with h | h
    · exact ⟨O, hO, h, Or.inl rfl⟩
    · refine ⟨O * Matrix.diagonal (sgn i₀), ?_, ?_, Or.inr rfl⟩
      · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Oᵀ, hO, Matrix.one_mul, hE]
      · rw [Matrix.det_mul, h, det_flip]; norm_num
  obtain ⟨O₁', h1', d1', hc1⟩ := hdet O₁ hO₁
  obtain ⟨O₂', h2', d2', hc2⟩ := hdet O₂ hO₂
  have e1 : ∃ v1, Z = rc O₁' * Matrix.diagonal v1 * (rc O₂)ᵀ := by
    rcases hc1 with h | h
    · subst h; exact ⟨v, hZ⟩
    · subst h; exact ⟨_, flipL i₀ O₁ O₂ v Z hZ⟩
  obtain ⟨v1, hv1⟩ := e1
  have e2 : ∃ v2, Z = rc O₁' * Matrix.diagonal v2 * (rc O₂')ᵀ := by
    rcases hc2 with h | h
    · subst h; exact ⟨v1, hv1⟩
    · subst h; exact ⟨_, flipR i₀ O₁' O₂ v1 Z hv1⟩
  obtain ⟨v2, hv2⟩ := e2
  exact ⟨O₁', O₂', v2, h1', h2', d1', d2', hv2⟩

end FormalResearch.FourQubitEntropy.PaperECritical
