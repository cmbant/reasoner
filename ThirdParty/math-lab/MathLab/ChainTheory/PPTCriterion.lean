module

/-
PPTCriterion.lean

**The PPT criterion in low dimensions** (Peres 1996; Horodecki, Horodecki and Horodecki 1996, with
Størmer's and Woronowicz's theorems): for `d₁, d₂ ≥ 2`, every PPT state on `ℂ^{d₁} ⊗ ℂ^{d₂}` is
separable exactly when `d₁ d₂ ≤ 6` (`ppt_criterion`).

  Part 1  The separable cone is closed. Its operators of trace at most one are the convex hull of 0 and
          the product states, a compact set (`MathLab.isCompact_convexHull`).
  Part 2  From maps to states: a Hermitian, block-positive `W` is the Choi matrix of a positive map
          (`choiInv`), and the Choi matrix of a decomposable map is nonnegative on PPT states. So if every
          positive map `Mₙ → Mₘ` is decomposable, Hahn–Banach leaves no PPT state outside the closed
          separable cone.
  Part 3  The criterion. With `Duality.lean`, every PPT state on `ℂⁿ ⊗ ℂᵐ` is separable exactly when
          every positive map `Mₙ → Mₘ` is decomposable, and the read cap (`Woronowicz.lean`) says when.
-/
public import MathLab.ChainTheory.Woronowicz
public import MathLab.Convex.CompactHull

@[expose] public section

open Matrix ComplexOrder Module

noncomputable section

namespace ChainPPT

open ChoiDark ChainReadCap ChainDuality ChainWoronowicz

variable {n m : ℕ}

/-! ## Part 1. The separable cone is closed -/

/-- The product projector `|x ⊗ y⟩⟨x ⊗ y|`. -/
def prodProj (x : Fin n → ℂ) (y : Fin m → ℂ) : Mat n m := vecMulVec (prodVec x y) (star (prodVec x y))

theorem isSeparable_prodProj (x : Fin n → ℂ) (y : Fin m → ℂ) : IsSeparable (prodProj x y) :=
  ⟨1, fun _ => x, fun _ => y, by simp [prodProj]⟩

theorem retr_prodProj (x : Fin n → ℂ) (y : Fin m → ℂ) :
    retr (prodProj x y) = (∑ a, Complex.normSq (x a)) * ∑ k, Complex.normSq (y k) := by
  simp only [retr, prodProj, vecMulVec_apply, prodVec, Pi.star_apply, Complex.re_sum,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [star_mul', Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem prodProj_smul_smul (x : Fin n → ℂ) (y : Fin m → ℂ) {c d : ℂ} (h : c * d = 1) :
    prodProj (c • x) (d • y) = prodProj x y := by
  have e : prodVec (c • x) (d • y) = prodVec x y := by
    funext z
    simp only [prodVec, Pi.smul_apply, smul_eq_mul]
    linear_combination (x z.1 * y z.2) * h
  rw [prodProj, e, prodProj]

theorem normSq_sum_smul {ι : Type*} [Fintype ι] (r : ℝ) (x : ι → ℂ) :
    ∑ i, Complex.normSq (((r : ℂ) • x) i) = r ^ 2 * ∑ i, Complex.normSq (x i) := by
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Product states: product projectors of trace one. -/
def prodStates (n m : ℕ) : Set (Mat n m) := {σ | (∃ x y, σ = prodProj x y) ∧ retr σ = 1}

theorem norm_le_one_of_normSq_sum {ι : Type*} [Fintype ι] {x : ι → ℂ}
    (h : ∑ i, Complex.normSq (x i) = 1) (i : ι) : ‖x i‖ ≤ 1 := by
  have h1 : Complex.normSq (x i) ≤ 1 :=
    h ▸ Finset.single_le_sum (f := fun j => Complex.normSq (x j)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  rw [← Complex.sq_norm] at h1
  nlinarith [norm_nonneg (x i)]

theorem isCompact_prodStates : IsCompact (prodStates n m) := by
  set Q : Set ((Fin n → ℂ) × (Fin m → ℂ)) :=
    {p | ∑ a, Complex.normSq (p.1 a) = 1 ∧ ∑ k, Complex.normSq (p.2 k) = 1}
  have hQc : IsCompact Q := by
    refine ((isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).prod
      (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset ?_ ?_
    · exact (isClosed_eq (continuous_finsetSum _ fun a _ =>
          Complex.continuous_normSq.comp ((continuous_apply a).comp continuous_fst)) continuous_const).inter
        (isClosed_eq (continuous_finsetSum _ fun k _ =>
          Complex.continuous_normSq.comp ((continuous_apply k).comp continuous_snd)) continuous_const)
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      refine ⟨fun a _ => ?_, fun k _ => ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_one_of_normSq_sum hx a
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_one_of_normSq_sum hy k
  have himg : prodStates n m = (fun p : (Fin n → ℂ) × (Fin m → ℂ) => prodProj p.1 p.2) '' Q := by
    ext σ
    constructor
    · rintro ⟨⟨x, y, rfl⟩, h1⟩
      rw [retr_prodProj] at h1
      set α := ∑ a, Complex.normSq (x a)
      have hα0 : 0 ≤ α := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg (x a)
      have hα : 0 < α := lt_of_le_of_ne hα0 fun h => by
        rw [← h, zero_mul] at h1
        exact zero_ne_one h1
      have hs : Real.sqrt α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
      refine ⟨((((Real.sqrt α)⁻¹ : ℝ) : ℂ) • x, ((Real.sqrt α : ℝ) : ℂ) • y), ⟨?_, ?_⟩, ?_⟩
      · show ∑ a, Complex.normSq (((((Real.sqrt α)⁻¹ : ℝ) : ℂ) • x) a) = 1
        rw [normSq_sum_smul, inv_pow, Real.sq_sqrt hα.le, inv_mul_cancel₀ hα.ne']
      · show ∑ k, Complex.normSq ((((Real.sqrt α : ℝ) : ℂ) • y) k) = 1
        rw [normSq_sum_smul, Real.sq_sqrt hα.le, h1]
      · exact prodProj_smul_smul x y (by rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs, Complex.ofReal_one])
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, y, rfl⟩, by rw [retr_prodProj, hx, hy, mul_one]⟩
  rw [himg]
  refine hQc.image (continuous_matrix fun i j => ?_)
  simp only [prodProj, vecMulVec_apply, prodVec, Pi.star_apply]
  fun_prop

theorem isPSD_of_isSeparable {ρ : Mat n m} (h : IsSeparable ρ) : IsPSD ρ := by
  obtain ⟨r, x, y, rfl⟩ := h
  exact Finset.sum_induction _ IsPSD (fun _ _ => IsPSD.add) isPSD_zero fun s _ => isPSD_rank_one _

theorem retr_sum {ι : Type*} (t : Finset ι) (X : ι → Mat n m) :
    retr (∑ i ∈ t, X i) = ∑ i ∈ t, retr (X i) := by
  simp only [retr, Matrix.sum_apply, Complex.re_sum]
  exact Finset.sum_comm

theorem retr_zero : retr (0 : Mat n m) = 0 := by
  simp [retr]

theorem prodProj_ofReal_smul (r : ℝ) (x : Fin n → ℂ) (y : Fin m → ℂ) :
    prodProj ((r : ℂ) • x) y = (r ^ 2) • prodProj x y := by
  ext i j
  simp only [prodProj, vecMulVec_apply, prodVec, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul',
    Matrix.smul_apply, Complex.real_smul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- A nonzero product projector, rescaled to trace one, is a product state. -/
theorem inv_smul_prodProj_mem (x : Fin n → ℂ) (y : Fin m → ℂ) (h : retr (prodProj x y) ≠ 0) :
    (retr (prodProj x y))⁻¹ • prodProj x y ∈ prodStates n m := by
  have h0 : 0 ≤ (retr (prodProj x y))⁻¹ := inv_nonneg.2 (isPSD_rank_one _).retr_nonneg
  refine ⟨⟨((Real.sqrt (retr (prodProj x y))⁻¹ : ℝ) : ℂ) • x, y, ?_⟩, ?_⟩
  · rw [prodProj_ofReal_smul, Real.sq_sqrt h0]
  · rw [retr_smul, inv_mul_cancel₀ h]

/-- The separable operators of trace at most one. -/
def sepBall (n m : ℕ) : Set (Mat n m) := {σ | IsSeparable σ ∧ retr σ ≤ 1}

theorem convex_separable : Convex ℝ {σ : Mat n m | IsSeparable σ} :=
  fun _ hx _ hy _ _ ha hb _ => isSeparable_add (isSeparable_smul hx ha) (isSeparable_smul hy hb)

theorem convex_sepBall : Convex ℝ (sepBall n m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨isSeparable_add (isSeparable_smul hx.1 ha) (isSeparable_smul hy.1 hb), ?_⟩
  rw [retr_add, retr_smul, retr_smul]
  nlinarith [hx.2, hy.2]

/-- **Separable operators of trace at most one are the convex hull of 0 and the product states.** -/
theorem sepBall_eq : sepBall n m = convexHull ℝ (insert 0 (prodStates n m)) := by
  apply Set.Subset.antisymm
  · rintro σ ⟨hσ, h1⟩
    obtain ⟨r, x, y, rfl⟩ := id hσ
    set t : Fin r → ℝ := fun s => retr (prodProj (x s) (y s))
    have ht0 : ∀ s, 0 ≤ t s := fun s => (isPSD_rank_one _).retr_nonneg
    have hz : ∀ s, (t s)⁻¹ • prodProj (x s) (y s) ∈ convexHull ℝ (insert 0 (prodStates n m)) := by
      intro s
      apply subset_convexHull
      by_cases h : t s = 0
      · rw [h, _root_.inv_zero, zero_smul]
        exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (inv_smul_prodProj_mem _ _ h)
    have hterm : ∀ s, t s • ((t s)⁻¹ • prodProj (x s) (y s)) = prodProj (x s) (y s) := by
      intro s
      by_cases h : t s = 0
      · rw [h, zero_smul]
        exact (eq_zero_of_retr (isPSD_rank_one _) h).symm
      · exact smul_inv_smul₀ h _
    have hsum : ∑ s, vecMulVec (prodVec (x s) (y s)) (star (prodVec (x s) (y s)))
        = ∑ s, t s • ((t s)⁻¹ • prodProj (x s) (y s)) :=
      Finset.sum_congr rfl fun s _ => (hterm s).symm
    have hT : retr (∑ s, vecMulVec (prodVec (x s) (y s)) (star (prodVec (x s) (y s)))) = ∑ s, t s :=
      retr_sum _ _
    by_cases hT0 : ∑ s, t s = 0
    · rw [eq_zero_of_retr (isPSD_of_isSeparable hσ) (hT.trans hT0)]
      exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · have hTpos : 0 < ∑ s, t s := lt_of_le_of_ne (Finset.sum_nonneg fun s _ => ht0 s) (Ne.symm hT0)
      have hmem : ∑ s, (t s / ∑ s, t s) • ((t s)⁻¹ • prodProj (x s) (y s))
          ∈ convexHull ℝ (insert 0 (prodStates n m)) :=
        (convex_convexHull ℝ _).sum_mem (fun s _ => div_nonneg (ht0 s) hTpos.le)
          (by rw [← Finset.sum_div, div_self hT0]) fun s _ => hz s
      have he : ∑ s, vecMulVec (prodVec (x s) (y s)) (star (prodVec (x s) (y s)))
          = (∑ s, t s) • ∑ s, (t s / ∑ s, t s) • ((t s)⁻¹ • prodProj (x s) (y s)) := by
        rw [hsum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_smul (∑ s, t s)]
        congr 1
        field_simp
      rw [he]
      exact (convex_convexHull ℝ _).smul_mem_of_zero_mem (subset_convexHull ℝ _ (Set.mem_insert _ _)) hmem
        ⟨hTpos.le, hT ▸ h1⟩
  · refine convexHull_min ?_ convex_sepBall
    rintro σ (rfl | ⟨⟨x, y, rfl⟩, h1⟩)
    · exact ⟨isSeparable_zero, by rw [retr_zero]; norm_num⟩
    · exact ⟨isSeparable_prodProj x y, h1.le⟩

theorem isCompact_sepBall : IsCompact (sepBall n m) := by
  rw [sepBall_eq]
  exact MathLab.isCompact_convexHull (isCompact_prodStates.insert 0)

/-- **The separable cone is closed.** -/
theorem isClosed_separable : IsClosed {σ : Mat n m | IsSeparable σ} := by
  refine isClosed_of_closure_subset fun X hX => ?_
  set R : ℝ := |retr X| + 1
  have hR : 0 < R := by positivity
  have hU : IsOpen {Y : Mat n m | retr Y < R} := isOpen_lt continuous_retr continuous_const
  have hXU : X ∈ {Y : Mat n m | retr Y < R} := show retr X < R by linarith [le_abs_self (retr X)]
  have h1 := hU.inter_closure ⟨hXU, hX⟩
  have hK : IsClosed ((fun Y : Mat n m => R • Y) '' sepBall n m) :=
    (isCompact_sepBall.image (continuous_const_smul R)).isClosed
  have hsub : {Y : Mat n m | retr Y < R} ∩ {σ | IsSeparable σ}
      ⊆ (fun Y : Mat n m => R • Y) '' sepBall n m := by
    rintro Y ⟨hY, hS⟩
    refine ⟨R⁻¹ • Y, ⟨isSeparable_smul hS (inv_nonneg.2 hR.le), ?_⟩, smul_inv_smul₀ hR.ne' Y⟩
    rw [retr_smul, inv_mul_le_iff₀ hR, mul_one]
    exact (show retr Y < R from hY).le
  obtain ⟨Z, hZ, hZX⟩ := closure_minimal hsub hK h1
  rw [Set.mem_ofPred_eq, ← hZX]
  exact isSeparable_smul hZ.1 hR.le

/-! ## Part 2. From maps to states -/

theorem pair_add_right (ρ X Y : Mat n m) : pair ρ (X + Y) = pair ρ X + pair ρ Y := by
  simp only [pair, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem pair_sum_right {ι : Type*} (t : Finset ι) (ρ : Mat n m) (X : ι → Mat n m) :
    pair ρ (∑ i ∈ t, X i) = ∑ i ∈ t, pair ρ (X i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [pair]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_right, ih]

theorem pair_comm (A B : Mat n m) : pair A B = pair B A := by
  simp only [pair]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The map with Choi matrix `W`: `Φ(X)ₖₗ = Σ_{a,b} X_{ab} W_{(a,k),(b,l)}`. -/
def choiInv (W : Mat n m) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := Matrix.of fun k l => ∑ a, ∑ b, X a b * W (a, k) (b, l)
  map_add' X Y := by
    ext k l
    simp only [Matrix.of_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext k l
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem choi_choiInv (W : Mat n m) : choi (choiInv W) = W := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [choi, choiInv, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.single_apply, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun c _ hc => Finset.sum_eq_zero fun d _ => ite_eq_right fun h => hc h.1.symm)
      (by simp),
    Finset.sum_eq_single b (fun d _ hd => ite_eq_right fun h => hd h.2.symm) (by simp), ite_eq_left ⟨rfl, rfl⟩]

theorem conjTranspose_mul_self_eq_sum {r : ℕ} (B : Matrix (Fin r) (Fin n) ℂ) :
    Bᴴ * B = ∑ s, vecMulVec (star (B s)) (B s) := by
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

/-- **A Hermitian, block-positive matrix is the Choi matrix of a positive map.** -/
theorem isPositive_choiInv {W : Mat n m} (hW : Wᴴ = W)
    (hbp : ∀ x y, 0 ≤ (star (prodVec x y) ⬝ᵥ (W *ᵥ prodVec x y)).re) : IsPositive (choiInv W) := by
  intro r B w
  have e : star w ⬝ᵥ (choiInv W (Bᴴ * B) *ᵥ w) = ∑ s, star (prodVec (B s) w) ⬝ᵥ (W *ᵥ prodVec (B s) w) := by
    rw [conjTranspose_mul_self_eq_sum, map_sum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← choi_prodVec, choi_choiInv]
  rw [e, Complex.re_sum, Complex.im_sum]
  exact ⟨Finset.sum_nonneg fun s _ => hbp _ _, Finset.sum_eq_zero fun s _ => im_quad_of_hermitian hW _⟩

/-- The Choi matrix of a map in Kraus form `Σ K · Kᴴ + Σ L ·ᵀ Lᴴ` is `P + pt Q`, with `P` and `Q` sums of
rank-one projectors. -/
theorem choi_eq_of_kraus {p q : ℕ} (K : Fin p → Matrix (Fin m) (Fin n) ℂ)
    (L : Fin q → Matrix (Fin m) (Fin n) ℂ) {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ) :
    choi Φ = ∑ k, vecMulVec (fun z : Idx n m => K k z.2 z.1) (star fun z : Idx n m => K k z.2 z.1)
      + pt (∑ l, vecMulVec (fun z : Idx n m => star (L l z.2 z.1))
          (star fun z : Idx n m => star (L l z.2 z.1))) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [choi, hΦ, Matrix.add_apply, Matrix.sum_apply, kEK_apply, LEtL_apply, pt, vecMulVec_apply,
    Pi.star_apply, star_star]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **The Choi matrix of a decomposable map is nonnegative on PPT operators.** -/
theorem pair_choi_nonneg_of_decomposable
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hΦ : IsDecomposable Φ)
    {ρ : Mat n m} (hρ : IsPPT ρ) : 0 ≤ (pair ρ (choi Φ)).re := by
  obtain ⟨p, q, K, L, hKL⟩ := hΦ
  rw [choi_eq_of_kraus K L hKL, pair_add_right, pair_pt, pair_sum_right, pair_sum_right, Complex.add_re,
    Complex.re_sum, Complex.re_sum]
  exact add_nonneg (Finset.sum_nonneg fun k _ => by rw [pair_rank_one]; exact (hρ.1 _).1)
    (Finset.sum_nonneg fun l _ => by rw [pair_rank_one]; exact (hρ.2 _).1)

/-- **Maps to states**: if every positive map `Mₙ → Mₘ` is decomposable, every PPT operator on
`ℂⁿ ⊗ ℂᵐ` is separable. A PPT operator outside the closed separable cone would be separated from it by a
block-positive Hermitian `W`, the Choi matrix of a positive map; that map is decomposable, so `W` is
nonnegative on the operator. -/
theorem allPPTSeparable_of_allDecomposable (h : AllDecomposable n m) : AllPPTSeparable n m := by
  intro ρ hρ
  by_contra hS
  obtain ⟨f, u, hfρ, hfS⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) convex_separable isClosed_separable hS
  simp only [RCLike.re_to_complex] at hfρ hfS
  have hu : u < 0 := by simpa using hfS 0 isSeparable_zero
  -- the separating functional is nonnegative on the cone
  have hpos : ∀ σ : Mat n m, IsSeparable σ → 0 ≤ (f σ).re := by
    intro b hb
    by_contra hneg
    push Not at hneg
    have ht : 0 < u / (f b).re := div_pos_of_neg_of_neg hu hneg
    have := hfS ((u / (f b).re) • b) (isSeparable_smul hb ht.le)
    rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  obtain ⟨W, hWH, hW⟩ := exists_hermitian_pair f
  have hbp : ∀ x y, 0 ≤ (star (prodVec x y) ⬝ᵥ (W *ᵥ prodVec x y)).re := fun x y => by
    rw [← pair_rank_one, hW _ (isPSD_rank_one _).hermitian]
    exact hpos _ (isSeparable_prodProj x y)
  have h1 := pair_choi_nonneg_of_decomposable (h (choiInv W) (isPositive_choiInv hWH hbp)) hρ
  rw [choi_choiInv, pair_comm, hW _ hρ.1.hermitian] at h1
  linarith

/-! ## Part 3. The PPT criterion -/

/-- **States and maps** (Horodecki, Horodecki and Horodecki 1996): every PPT operator on `ℂⁿ ⊗ ℂᵐ` is
separable exactly when every positive map `Mₙ → Mₘ` is decomposable. -/
theorem allPPTSeparable_iff_allDecomposable : AllPPTSeparable n m ↔ AllDecomposable n m :=
  ⟨allDecomposable_of_allPPTSeparable, allPPTSeparable_of_allDecomposable⟩

/-- Swapping the two factors. -/
theorem allPPTSeparable_symm (h : AllPPTSeparable n m) : AllPPTSeparable m n :=
  allPPTSeparable_of_allDecomposable (allDecomposable_symm (allDecomposable_of_allPPTSeparable h))

/-- **Woronowicz's theorem, state form**: every PPT operator on `ℂ² ⊗ ℂ³` is separable. -/
theorem pptSeparable23 : AllPPTSeparable 2 3 :=
  allPPTSeparable_of_allDecomposable woronowicz

/-- Every PPT operator on `ℂ³ ⊗ ℂ²` is separable. -/
theorem pptSeparable32 : AllPPTSeparable 3 2 :=
  allPPTSeparable_symm pptSeparable23

/-- **The PPT criterion**: for `d₁, d₂ ≥ 2`, every PPT operator on `ℂ^{d₁} ⊗ ℂ^{d₂}` is separable exactly
when `d₁ d₂ ≤ 6`. -/
theorem ppt_criterion {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) :
    AllPPTSeparable d₁ d₂ ↔ d₁ * d₂ ≤ 6 := by
  rw [allPPTSeparable_iff_allDecomposable, ← readable_iff_allDecomposable]
  exact readcap d₁ d₂ h₁ h₂

/-- **PPT entangled states exist** on `ℂ^{d₁} ⊗ ℂ^{d₂}` whenever `d₁, d₂ ≥ 2` and `d₁ d₂ > 6`. -/
theorem exists_ppt_entangled {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) (h : 6 < d₁ * d₂) :
    ∃ ρ : Mat d₁ d₂, IsPPT ρ ∧ ¬ IsSeparable ρ := by
  have hn : ¬ AllPPTSeparable d₁ d₂ := fun hs => absurd ((ppt_criterion h₁ h₂).1 hs) (by omega)
  unfold AllPPTSeparable at hn
  push Not at hn
  exact hn

theorem pt_sum {ι : Type*} (t : Finset ι) (X : ι → Mat n m) :
    pt (∑ i ∈ t, X i) = ∑ i ∈ t, pt (X i) := by
  ext x y
  simp only [pt, Matrix.sum_apply]

theorem pt_prodProj (x : Fin n → ℂ) (y : Fin m → ℂ) : pt (prodProj x y) = prodProj x (star y) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [pt, prodProj, vecMulVec_apply, prodVec, Pi.star_apply, star_mul', star_star]
  ring

/-- **Peres's criterion**: separable operators are PPT. -/
theorem isPPT_of_isSeparable {ρ : Mat n m} (h : IsSeparable ρ) : IsPPT ρ := by
  refine ⟨isPSD_of_isSeparable h, ?_⟩
  obtain ⟨r, x, y, rfl⟩ := h
  have e : pt (∑ s, vecMulVec (prodVec (x s) (y s)) (star (prodVec (x s) (y s))))
      = ∑ s, prodProj (x s) (star (y s)) := by
    rw [pt_sum]
    exact Finset.sum_congr rfl fun s _ => pt_prodProj (x s) (y s)
  rw [e]
  exact isPSD_of_isSeparable ⟨r, x, fun s => star (y s), rfl⟩

/-- **In dimensions `d₁ d₂ ≤ 6`, an operator is separable exactly when it is PPT.** -/
theorem isSeparable_iff_isPPT {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) (h : d₁ * d₂ ≤ 6)
    (ρ : Mat d₁ d₂) : IsSeparable ρ ↔ IsPPT ρ :=
  ⟨isPPT_of_isSeparable, (ppt_criterion h₁ h₂).2 h ρ⟩

/-! ### An explicit PPT entangled state

`ChoiDark.rhoQ` is a rational PPT state on `ℂ³ ⊗ ℂ³` on which the Choi map's Choi matrix is negative.
In the vocabulary of this file it is PPT and not separable, a concrete instance of
`exists_ppt_entangled`. -/

/-- A matrix given as a nonnegative rational sum of rank-one terms is positive semidefinite. -/
theorem isPSD_of_rat_sum {ι : Type*} [Fintype ι] {N : ℕ} (c : Fin N → ℚ) (hc : ∀ k, 0 ≤ c k)
    (v : Fin N → ι → ℚ) {M : Matrix ι ι ℂ} (hM : ∀ s t, M s t = ∑ k, ((c k * v k s * v k t : ℚ) : ℂ)) :
    IsPSD M := by
  have e : M = ∑ k, ((c k : ℝ)) • vecMulVec (fun s => (v k s : ℂ)) (star fun s => (v k s : ℂ)) := by
    ext s t
    rw [hM, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, star_ratC, Complex.real_smul]
    push_cast
    ring
  rw [e]
  exact Finset.sum_induction _ IsPSD (fun _ _ => IsPSD.add) isPSD_zero
    fun k _ => (isPSD_rank_one _).smul (by exact_mod_cast hc k)

/-- The state `ChoiDark.rhoQ` as an operator on `ℂ³ ⊗ ℂ³`. -/
def rho33 : Mat 3 3 := fun s t => (rhoQ s t : ℂ)

/-- **An explicit PPT entangled state on `ℂ³ ⊗ ℂ³`.** -/
theorem rho33_ppt_entangled : IsPPT rho33 ∧ ¬ IsSeparable rho33 := by
  refine ⟨⟨isPSD_of_rat_sum rhoWt rho_ppt.1 rhoVec fun s t => ?_,
    isPSD_of_rat_sum ptWt rho_ppt.2.1 ptVec fun s t => ?_⟩, ?_⟩
  · simp only [rho33, rhoQ]
    push_cast
    rfl
  · simp only [pt, rho33]
    rw [rho_partialTranspose]
    push_cast
    rfl
  · rintro ⟨r, x, y, h⟩
    refine rho_entangled ⟨r, fun _ => 1, x, y, fun _ => zero_le_one, fun s t => ?_⟩
    have := congrFun (congrFun h s) t
    simp only [rho33, Matrix.sum_apply, vecMulVec_apply, prodVec, Pi.star_apply] at this
    rw [this]
    simp

/-- The matrix unit `single a b 1` of `M₂` is `ChoiDark.E2 a b`. -/
theorem single_eq_E2 (a b : Fin 2) : single a b (1 : ℂ) = E2 a b := by
  ext r c
  fin_cases a <;> fin_cases b <;> fin_cases r <;> fin_cases c <;> simp [E2]

/-- The Choi matrix of `ChoiDark.phi24` is the integer witness `W24`. -/
theorem choi_phi24 (x y : Idx 2 4) : choi phi24Lin x y = (W24 (ix x.1 x.2) (ix y.1 y.2) : ℂ) := by
  rw [← phi24_E, ← single_eq_E2]
  rfl

/-- P. Horodecki's state `ChoiDark.rho24` (b = 3/5) as an operator on `ℂ² ⊗ ℂ⁴`. -/
def rho24M : Mat 2 4 := fun x y => (rho24 x.1 x.2 y.1 y.2 : ℂ)

/-- **An explicit PPT entangled state on `ℂ² ⊗ ℂ⁴`**: the Choi matrix of the positive map `phi24` is
negative on it. -/
theorem rho24M_ppt_entangled : IsPPT rho24M ∧ ¬ IsSeparable rho24M := by
  refine ⟨⟨isPSD_of_rat_sum rho24Wt rho24_weights_nonneg.1 (fun j x => rho24Vec j (ix x.1 x.2))
      fun s t => ?_, isPSD_of_rat_sum pt24Wt rho24_weights_nonneg.2 (fun j x => pt24Vec j (ix x.1 x.2))
      fun s t => ?_⟩, fun hs => ?_⟩
  · simp only [rho24M, rho24]
    push_cast
    rfl
  · simp only [pt, rho24M]
    rw [rho24_pt]
    push_cast
    rfl
  · have h := pair_choi_nonneg_of_separable hs (Φ := phi24Lin) fun _ B w => phi24_positive_psd B w
    have hv : pair rho24M (choi phi24Lin) = -1 := by
      have := congrArg (fun q : ℚ => (q : ℂ)) rho24_witness_value
      push_cast at this
      rw [← this]
      simp only [pair, rho24M, choi_phi24]
      rw [Finset.sum_comm]
      simp only [Fintype.sum_prod_type]
    rw [hv] at h
    norm_num at h

end ChainPPT

end

end -- public section

#print axioms ChainPPT.isClosed_separable
#print axioms ChainPPT.isPositive_choiInv
#print axioms ChainPPT.pair_choi_nonneg_of_decomposable
#print axioms ChainPPT.allPPTSeparable_of_allDecomposable
#print axioms ChainPPT.allPPTSeparable_iff_allDecomposable
#print axioms ChainPPT.pptSeparable23
#print axioms ChainPPT.ppt_criterion
#print axioms ChainPPT.exists_ppt_entangled
#print axioms ChainPPT.isPPT_of_isSeparable
#print axioms ChainPPT.isSeparable_iff_isPPT
#print axioms ChainPPT.rho33_ppt_entangled
#print axioms ChainPPT.rho24M_ppt_entangled
