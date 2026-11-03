import FormalResearch.GurvitsBarnum.ContractionPolar

/-!
# Gurvits–Barnum: positive maps preserve the adjoint and contractions (L1, L3)

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002); plan lemmas L1, L2, L3.

Headlines, for a linear map `φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ` with `IsPositiveMap φ`
(defined in `ContractionBase`):

* `IsPositiveMap.map_conjTranspose` (L1): `φ Xᴴ = (φ X)ᴴ`.
* `IsPositiveMap.contraction` (L3, Russo–Dye in finite dimension): if `φ 1 = 1` and
  `1 - XᴴX ≥ 0` then `1 - (φ X)ᴴ (φ X) ≥ 0`.
* `IsPositiveMap.contraction_scaled`: the same with `c² • 1`, `c ≥ 0`.
* `IsPositiveMap.norm_dot_le`: the vector form `‖⟨u, φ X w⟩‖ ≤ c ‖u‖ ‖w‖` (Euclidean norms).

The proof of L3: L2 (a unital positive map sends a unitary to a contraction, by the spectral
theorem for unitaries and Cauchy–Schwarz twice) gives the invertible case through the
decomposition of an invertible contraction as an average of two unitaries; the general case
follows since `X + t·1` is invertible for all but finitely many `t` and the bound is closed.
-/

namespace FormalResearch.GurvitsBarnum

open Matrix ComplexOrder
open scoped MatrixOrder
open Contr

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-! ### L1 -/

theorem posSemidef_cdiag {W : Matrix n n ℂ} {a : n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (cdiag W (fun i => (a i : ℂ))).PosSemidef := by
  have : cdiag W (fun i => (a i : ℂ)) = (Wᴴ)ᴴ * diagonal (fun i => (a i : ℂ)) * Wᴴ := by
    simp [cdiag]
  rw [this]
  exact (PosSemidef.diagonal fun i => Complex.zero_le_real.2 (ha i)).conjTranspose_mul_mul_same _

theorem IsPositiveMap.isHermitian_map {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ}
    (hφ : IsPositiveMap φ) {H : Matrix n n ℂ} (hH : H.IsHermitian) : (φ H).IsHermitian := by
  obtain ⟨W, d, hW, hHd⟩ := exists_cdiag_of_isHermitian hH
  have hpt : ∀ x : ℝ, ((max x 0 : ℝ) : ℂ) - ((max (-x) 0 : ℝ) : ℂ) = x := by
    intro x
    rcases le_total x 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  have : H = cdiag W (fun i => ((max (d i) 0 : ℝ) : ℂ))
      - cdiag W (fun i => ((max (-d i) 0 : ℝ) : ℂ)) := by
    rw [cdiag_sub, hHd]
    congr 1
    funext i
    exact (hpt (d i)).symm
  rw [this, map_sub]
  exact (hφ _ (posSemidef_cdiag fun i => le_max_right _ _)).isHermitian.sub
    (hφ _ (posSemidef_cdiag fun i => le_max_right _ _)).isHermitian

/-- **L1** (Gurvits–Barnum, PRA 66, 062311, Sec. III; plan lemma L1): a positive linear map
between matrix algebras preserves the adjoint. -/
theorem IsPositiveMap.map_conjTranspose {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ}
    (hφ : IsPositiveMap φ) (X : Matrix n n ℂ) : φ Xᴴ = (φ X)ᴴ := by
  obtain ⟨A, B, hA, hB, hX⟩ : ∃ A B : Matrix n n ℂ, A.IsHermitian ∧ B.IsHermitian ∧
      X = A + Complex.I • B := by
    refine ⟨(1 / 2 : ℂ) • (X + Xᴴ), (-(Complex.I / 2)) • (X - Xᴴ), ?_, ?_, ?_⟩
    · simp [IsHermitian, conjTranspose_smul, conjTranspose_add, add_comm]
    · show ((-(Complex.I / 2)) • (X - Xᴴ))ᴴ = _
      simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
        Complex.star_def, map_neg, map_div₀, Complex.conj_I, map_ofNat]
      module
    · simp only [smul_smul]
      match_scalars <;>
        first
          | linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
          | linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  subst hX
  have hA' := (hφ.isHermitian_map hA).eq
  have hB' := (hφ.isHermitian_map hB).eq
  simp only [map_add, map_smul, conjTranspose_add, conjTranspose_smul, hA.eq, hB.eq, hA', hB',
    Complex.star_def, Complex.conj_I, neg_smul, map_neg]

/-! ### L3 -/

/-- A finite subset of `ℝ` misses some element of `(0, ε)`. -/
theorem exists_pos_lt_notMem {S : Set ℝ} (hS : S.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ t ∉ S := by
  obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite hε).exists_notMem_finset hS.toFinset
  exact ⟨t, ht.1, ht.2, by simpa using hnot⟩

/-- Only finitely many real `t` make `X + t·1` singular. -/
theorem finite_singular_shifts (X : Matrix n n ℂ) :
    {t : ℝ | (X + (t : ℂ) • (1 : Matrix n n ℂ)).det = 0}.Finite := by
  have hF := Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic X).ne_zero
  have hinj : Set.InjOn (fun t : ℝ => -(t : ℂ)) Set.univ := by
    intro a _ b _ h
    simpa using h
  refine (hF.preimage (hinj.mono (Set.subset_univ _))).subset ?_
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly]
  have : Matrix.scalar n (-(t : ℂ)) - X = -(X + (t : ℂ) • (1 : Matrix n n ℂ)) := by
    simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, diagonal_neg, sub_eq_add_neg,
      add_comm]
  rw [this, det_neg, ht, mul_zero]

/-- **L3 (vector form), Russo–Dye in finite dimension.** -/
theorem IsPositiveMap.bdd_map {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ} (hφ : IsPositiveMap φ)
    (h1 : φ 1 = 1) {X : Matrix n n ℂ} (hX : Bdd 1 X) : Bdd 1 (φ X) := by
  refine bdd_of_forall_pos fun ε hε => ?_
  obtain ⟨t, ht0, htε, htS⟩ := exists_pos_lt_notMem (finite_singular_shifts X) (half_pos hε)
  have ht1 : (0 : ℝ) < 1 + t := by linarith
  set Xt : Matrix n n ℂ := (((1 + t)⁻¹ : ℝ) : ℂ) • (X + (t : ℂ) • 1) with hXt
  have hb : Bdd 1 Xt := by
    have := bdd_smul ((1 + t)⁻¹) (inv_nonneg.2 ht1.le) (hX.add (bdd_smul_one ht0.le))
    rwa [inv_mul_cancel₀ ht1.ne'] at this
  have hdet : Xt.det ≠ 0 := by
    rw [hXt, det_smul]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · exact_mod_cast (inv_pos.2 ht1).ne'
    · exact htS
  have hmap := bdd_map_of_invertible φ hφ h1 hb hdet
  have heq : φ X = (((1 + t : ℝ)) : ℂ) • φ Xt + -((t : ℂ) • (1 : Matrix k k ℂ)) := by
    rw [hXt, map_smul, map_add, map_smul, h1, smul_smul]
    have : ((1 + t : ℝ) : ℂ) * (((1 + t)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ ht1.ne', Complex.ofReal_one]
    rw [this, one_smul]; abel
  rw [heq]
  have := (bdd_smul (1 + t) ht1.le hmap).add (bdd_smul_one ht0.le).neg
  refine this.mono ?_
  linarith

/-- **L3 (scaled vector form).** -/
theorem IsPositiveMap.bdd_map_scaled {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ} (hφ : IsPositiveMap φ)
    (h1 : φ 1 = 1) {c : ℝ} (hc : 0 ≤ c) {X : Matrix n n ℂ} (hX : Bdd c X) : Bdd c (φ X) := by
  refine bdd_of_forall_pos fun ε hε => ?_
  have hcε : 0 < c + ε := by linarith
  have hb : Bdd 1 ((((c + ε)⁻¹ : ℝ) : ℂ) • X) := by
    have := bdd_smul ((c + ε)⁻¹) (inv_nonneg.2 hcε.le) (hX.mono (le_add_of_nonneg_right hε.le))
    rwa [inv_mul_cancel₀ hcε.ne'] at this
  have hmap := hφ.bdd_map h1 hb
  rw [map_smul] at hmap
  have := bdd_smul (c + ε) hcε.le hmap
  rwa [mul_one, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hcε.ne', Complex.ofReal_one,
    one_smul] at this

/-- **L3** (Gurvits–Barnum, PRA 66, 062311, Prop. 2; plan lemma L3), scaled form: a unital
positive map sends a matrix with `c² 1 - XᴴX ≥ 0` to one with `c² 1 - (φ X)ᴴ (φ X) ≥ 0`. -/
theorem IsPositiveMap.contraction_scaled {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ}
    (hφ : IsPositiveMap φ) (h1 : φ 1 = 1) {c : ℝ} (hc : 0 ≤ c) {X : Matrix n n ℂ}
    (hX : (((c ^ 2 : ℝ)) • (1 : Matrix n n ℂ) - Xᴴ * X).PosSemidef) :
    (((c ^ 2 : ℝ)) • (1 : Matrix k k ℂ) - (φ X)ᴴ * φ X).PosSemidef :=
  psd_of_bdd hc (hφ.bdd_map_scaled h1 hc (bdd_of_psd hc hX))

/-- **L3** (Gurvits–Barnum, PRA 66, 062311, Prop. 2; plan lemma L3, Russo–Dye in finite
dimension): a unital positive map sends a contraction to a contraction. -/
theorem IsPositiveMap.contraction {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ}
    (hφ : IsPositiveMap φ) (h1 : φ 1 = 1) {X : Matrix n n ℂ}
    (hX : (1 - Xᴴ * X).PosSemidef) : (1 - (φ X)ᴴ * φ X).PosSemidef := by
  have := hφ.contraction_scaled h1 zero_le_one (X := X) (by simpa using hX)
  simpa using this

/-- **L3, vector form** (Gurvits–Barnum, PRA 66, 062311; plan lemma L3): if `c² 1 - XᴴX ≥ 0`
then `‖⟨u, φ(X) w⟩‖ ≤ c ‖u‖ ‖w‖` with Euclidean norms. -/
theorem IsPositiveMap.norm_dot_le {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ}
    (hφ : IsPositiveMap φ) (h1 : φ 1 = 1) {c : ℝ} (hc : 0 ≤ c) {X : Matrix n n ℂ}
    (hX : (((c ^ 2 : ℝ)) • (1 : Matrix n n ℂ) - Xᴴ * X).PosSemidef) (u w : k → ℂ) :
    ‖star u ⬝ᵥ (φ X *ᵥ w)‖ ≤
      c * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ k)‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ k)‖ :=
  hφ.bdd_map_scaled h1 hc (bdd_of_psd hc hX) u w

/-- **L3, vector form with a vector-form hypothesis**: if `‖⟨u, X w⟩‖ ≤ c ‖u‖ ‖w‖` for all
`u, w` then the same holds for `φ X`. -/
theorem IsPositiveMap.norm_dot_le_of_norm_dot_le {φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ}
    (hφ : IsPositiveMap φ) (h1 : φ 1 = 1) {c : ℝ} (hc : 0 ≤ c) {X : Matrix n n ℂ}
    (hX : ∀ u w : n → ℂ, ‖star u ⬝ᵥ (X *ᵥ w)‖ ≤
      c * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖)
    (u w : k → ℂ) :
    ‖star u ⬝ᵥ (φ X *ᵥ w)‖ ≤
      c * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ k)‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ k)‖ :=
  hφ.bdd_map_scaled h1 hc hX u w

/-- info: 'FormalResearch.GurvitsBarnum.IsPositiveMap.map_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.map_conjTranspose

/-- info: 'FormalResearch.GurvitsBarnum.IsPositiveMap.contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.contraction

/-- info: 'FormalResearch.GurvitsBarnum.IsPositiveMap.contraction_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.contraction_scaled

/-- info: 'FormalResearch.GurvitsBarnum.IsPositiveMap.norm_dot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.norm_dot_le

/-- info: 'FormalResearch.GurvitsBarnum.IsPositiveMap.norm_dot_le_of_norm_dot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsPositiveMap.norm_dot_le_of_norm_dot_le

end FormalResearch.GurvitsBarnum
