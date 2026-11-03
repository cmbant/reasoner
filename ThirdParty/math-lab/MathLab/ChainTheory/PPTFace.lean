module

/-
PPTFace.lean

A dimension count for extreme rays of the PPT cone (the face argument behind Hildebrand's bound, as used
by Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman, Oper. Matrices 3 (2009), Lemma 5.3).

If `ρ = Fᴴ F` and `pt ρ = F'ᴴ F'`, every Hermitian `σ` of the form `Fᴴ H F` with `pt σ = F'ᴴ H' F'` is a
direction in which `ρ ± ε σ` stays PPT. The space of such `σ` has complex dimension at least
`r² + s² - D²`, where `r` and `s` count independent vectors in the ranges of `Fᴴ` and `F'ᴴ` and `D` is
the dimension of the space. On an extreme ray it is spanned by `ρ`, so `r² + s² ≤ D² + 1`
(`extreme_rank_bound`). For ℂ² ⊗ ℂ³ this is `r² + s² ≤ 37`.
-/
public import MathLab.ChainTheory.WoronowiczBase

@[expose] public section

open Matrix ComplexOrder Module

noncomputable section

namespace ChainWoronowicz

open ChoiDark ChainReadCap ChainDuality

variable {n m : ℕ}

/-- `1 ± t H ⪰ 0` for small `t` when `H` is Hermitian. -/
theorem exists_isPSD_one_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : Hᴴ = H) : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → IsPSD (1 + (t : ℂ) • H) := by
  set K : ℝ := ∑ i, ∑ j, ‖H i j‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 / (K + 1), by positivity, fun t ht v => ?_⟩
  set S : ℝ := ∑ i, ‖v i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : star v ⬝ᵥ ((1 + (t : ℂ) • H) *ᵥ v) = (S : ℂ) + (t : ℂ) * (star v ⬝ᵥ (H *ᵥ v)) := by
    rw [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, hS]
    congr 1
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  have him : (star v ⬝ᵥ (H *ᵥ v)).im = 0 := im_quad_of_hermitian hH v
  have hvv : ∀ i j, ‖v i‖ * ‖v j‖ ≤ S := by
    intro i j
    have hi : ‖v i‖ ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hj : ‖v j‖ ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith [norm_nonneg (v i), norm_nonneg (v j), sq_nonneg (‖v i‖ - ‖v j‖)]
  have hb : ‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ K * S := by
    calc ‖star v ⬝ᵥ (H *ᵥ v)‖ = ‖∑ i, ∑ j, star (v i) * (H i j * v j)‖ := by
          simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, ‖star (v i) * (H i j * v j)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
      _ = ∑ i, ∑ j, ‖H i j‖ * (‖v i‖ * ‖v j‖) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_mul, norm_star]
          ring
      _ ≤ ∑ i, ∑ j, ‖H i j‖ * S :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hvv i j) (norm_nonneg _)
      _ = K * S := by rw [hK, Finset.sum_mul]; simp only [Finset.sum_mul]
  have hre : |(star v ⬝ᵥ (H *ᵥ v)).re| ≤ K * S :=
    (Complex.abs_re_le_norm _).trans hb
  rw [hq]
  refine ⟨?_, by simp [him]⟩
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have htK : |t| * K ≤ 1 := by
    have h1 : |t| * K ≤ K / (K + 1) := by
      calc |t| * K ≤ 1 / (K + 1) * K := mul_le_mul_of_nonneg_right ht hK0
        _ = K / (K + 1) := by ring
    have h2 : K / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have : |t * (star v ⬝ᵥ (H *ᵥ v)).re| ≤ S := by
    rw [abs_mul]
    calc |t| * |(star v ⬝ᵥ (H *ᵥ v)).re| ≤ |t| * (K * S) :=
          mul_le_mul_of_nonneg_left hre (abs_nonneg t)
      _ = (|t| * K) * S := by ring
      _ ≤ 1 * S := mul_le_mul_of_nonneg_right htK hS0
      _ = S := one_mul S
  linarith [neg_abs_le (t * (star v ⬝ᵥ (H *ᵥ v)).re)]

theorem isPPT_smul {ρ : Mat n m} (h : IsPPT ρ) {t : ℝ} (ht : 0 ≤ t) : IsPPT (t • ρ) :=
  ⟨h.1.smul ht, by rw [pt_smul]; exact h.2.smul ht⟩

theorem pt_conjTranspose (X : Mat n m) : pt Xᴴ = (pt X)ᴴ := rfl

/-- Independent columns: `U X = 0` forces `X = 0`. -/
theorem eq_zero_of_mul_eq_zero_left {ι κ : Type*} [Fintype ι] {r : ℕ} {U : Matrix ι (Fin r) ℂ}
    (hU : LinearIndependent ℂ (fun i => fun x => U x i)) {X : Matrix (Fin r) κ ℂ} (h : U * X = 0) :
    X = 0 := by
  ext i j
  have h' : ∑ i, X i j • (fun x => U x i) = 0 := by
    ext x
    have := congrFun (congrFun h x) j
    simp only [Matrix.mul_apply, Matrix.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact Fintype.linearIndependent_iff.1 hU (fun i => X i j) h' i

/-- The ℂ-linear partial transpose, an involution. -/
def ptEquiv : Mat n m ≃ₗ[ℂ] Mat n m :=
  LinearEquiv.ofInvolutive ⟨⟨pt, pt_add⟩, fun _ _ => rfl⟩ (fun _ => rfl)

/-- The sandwich map `Y ↦ Fᴴ Y F`. -/
def sandwich (F : Mat n m) : Mat n m →ₗ[ℂ] Mat n m where
  toFun Y := Fᴴ * Y * F
  map_add' _ _ := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' _ _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem sandwich_apply (F Y : Mat n m) : sandwich F Y = Fᴴ * Y * F := rfl

/-- `r` independent vectors in the range of `Fᴴ` give an `r²`-dimensional space of sandwiches. -/
theorem finrank_range_sandwich_ge (F : Mat n m) {r : ℕ} (u : Fin r → Idx n m → ℂ)
    (hu : LinearIndependent ℂ u) (hu' : ∀ i, ∃ w, u i = Fᴴ *ᵥ w) :
    r * r ≤ finrank ℂ (LinearMap.range (sandwich F)) := by
  choose w hw using hu'
  set U : Matrix (Idx n m) (Fin r) ℂ := of fun x i => u i x with hUdef
  set W : Matrix (Idx n m) (Fin r) ℂ := of fun x i => w i x with hWdef
  have hUW : U = Fᴴ * W := by
    ext x i
    simp only [hUdef, hWdef, of_apply, hw i, mulVec, dotProduct, Matrix.mul_apply]
  have hcols : LinearIndependent ℂ (fun i => fun x => U x i) := by
    simpa only [hUdef, of_apply] using hu
  let Ψ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Mat n m :=
    { toFun := fun Z => U * Z * Uᴴ
      map_add' := fun _ _ => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun _ _ => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Z hZ
    have h1 : U * (Z * Uᴴ) = 0 := by rw [← Matrix.mul_assoc]; exact hZ
    have h2 := eq_zero_of_mul_eq_zero_left hcols h1
    have h3 : U * Zᴴ = 0 := by
      have := congrArg conjTranspose h2
      rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
    have h4 := eq_zero_of_mul_eq_zero_left hcols h3
    rw [← conjTranspose_conjTranspose Z, h4, conjTranspose_zero]
  have hle : LinearMap.range Ψ ≤ LinearMap.range (sandwich F) := by
    rintro _ ⟨Z, rfl⟩
    refine ⟨W * Z * Wᴴ, ?_⟩
    show Fᴴ * (W * Z * Wᴴ) * F = U * Z * Uᴴ
    rw [hUW, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  calc r * r = finrank ℂ (Matrix (Fin r) (Fin r) ℂ) := by simp [Module.finrank_matrix]
    _ = finrank ℂ (LinearMap.range Ψ) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ _ := Submodule.finrank_mono hle

/-- **The face bound**: on an extreme ray of the PPT cone, `r² + s² ≤ D² + 1`, where `r` and `s` count
independent vectors in the ranges of Gram factors of `ρ` and `pt ρ`, and `D = n m`. -/
theorem extreme_rank_bound {ρ : Mat n m} (hρ : IsExtremePPT ρ) (F F' : Mat n m)
    (hF : ρ = Fᴴ * F) (hF' : pt ρ = F'ᴴ * F') {r s : ℕ} (u : Fin r → Idx n m → ℂ)
    (hu : LinearIndependent ℂ u) (hu' : ∀ i, ∃ w, u i = Fᴴ *ᵥ w) (v : Fin s → Idx n m → ℂ)
    (hv : LinearIndependent ℂ v) (hv' : ∀ i, ∃ w, v i = F'ᴴ *ᵥ w) :
    r * r + s * s ≤ (n * m) * (n * m) + 1 := by
  by_contra hlt
  push Not at hlt
  set V₁ := LinearMap.range (sandwich F) with hV₁
  set V₂ := (LinearMap.range (sandwich F')).comap ptEquiv.toLinearMap with hV₂
  have h1 : r * r ≤ finrank ℂ V₁ := finrank_range_sandwich_ge F u hu hu'
  have h2 : s * s ≤ finrank ℂ V₂ := by
    have := finrank_range_sandwich_ge F' v hv hv'
    rw [hV₂, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact this
  have hdim : finrank ℂ (Mat n m) = (n * m) * (n * m) := by simp [Module.finrank_matrix]
  have h3 : finrank ℂ ↥(V₁ ⊔ V₂) ≤ (n * m) * (n * m) := hdim ▸ Submodule.finrank_le _
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  have h5 : 2 ≤ finrank ℂ ↥(V₁ ⊓ V₂) := by omega
  -- the intersection is closed under ᴴ
  have hstar : ∀ X ∈ V₁ ⊓ V₂, Xᴴ ∈ V₁ ⊓ V₂ := by
    rintro X ⟨⟨Y, hY⟩, ⟨Y', hY'⟩⟩
    refine ⟨⟨Yᴴ, ?_⟩, ⟨Y'ᴴ, ?_⟩⟩
    · rw [← hY, sandwich_apply, sandwich_apply, conjTranspose_mul, conjTranspose_mul,
        conjTranspose_conjTranspose, Matrix.mul_assoc]
    · show F'ᴴ * Y'ᴴ * F' = pt Xᴴ
      have h : pt X = F'ᴴ * Y' * F' := hY'.symm
      rw [pt_conjTranspose, h, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
  -- a Hermitian direction not along ρ
  have hherm : ∀ X : Mat n m, ((1 / 2 : ℂ) • (X + Xᴴ))ᴴ = (1 / 2 : ℂ) • (X + Xᴴ) := by
    intro X
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  obtain ⟨σ, hσ, hσH, hσρ⟩ : ∃ σ ∈ V₁ ⊓ V₂, σᴴ = σ ∧ ∀ c : ℝ, σ ≠ c • ρ := by
    by_contra hno
    push Not at hno
    have hsub : V₁ ⊓ V₂ ≤ Submodule.span ℂ {ρ} := by
      intro X hX
      have hXs := hstar X hX
      have hh : (1 / 2 : ℂ) • (X + Xᴴ) ∈ V₁ ⊓ V₂ :=
        Submodule.smul_mem _ _ (Submodule.add_mem _ hX hXs)
      have ha : (-Complex.I / 2) • (X - Xᴴ) ∈ V₁ ⊓ V₂ :=
        Submodule.smul_mem _ _ (Submodule.sub_mem _ hX hXs)
      have haH : ((-Complex.I / 2) • (X - Xᴴ))ᴴ = (-Complex.I / 2) • (X - Xᴴ) := by
        rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
        have hs : star (-Complex.I / 2) = -(-Complex.I / 2) := by
          apply Complex.ext <;> norm_num
        rw [hs, neg_smul, ← smul_neg, neg_sub]
      obtain ⟨a, ha'⟩ := hno _ hh (hherm X)
      obtain ⟨b, hb'⟩ := hno _ ha haH
      rw [Submodule.mem_span_singleton]
      refine ⟨(a : ℂ) + Complex.I * b, ?_⟩
      have hX : X = (1 / 2 : ℂ) • (X + Xᴴ) + Complex.I • ((-Complex.I / 2) • (X - Xᴴ)) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hX, ha', hb', add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    have h6 := Submodule.finrank_mono hsub
    have hsp : finrank ℂ (Submodule.span ℂ ({ρ} : Set (Mat n m))) ≤ 1 := by
      simpa using finrank_span_le_card ({ρ} : Set (Mat n m))
    omega
  -- σ = Fᴴ H F and pt σ = F'ᴴ H' F' with H, H' Hermitian
  obtain ⟨⟨Y, hY⟩, ⟨Y', hY'⟩⟩ := hσ
  rw [sandwich_apply] at hY
  change F'ᴴ * Y' * F' = pt σ at hY'
  have hhalf : ∀ X : Mat n m, (1 / 2 : ℂ) • (X + X) = X := by
    intro X
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hσF : σ = Fᴴ * ((1 / 2 : ℂ) • (Y + Yᴴ)) * F := by
    have e1 : σᴴ = Fᴴ * Yᴴ * F := by
      rw [← hY, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    calc σ = (1 / 2 : ℂ) • (σ + σᴴ) := by rw [hσH, hhalf]
      _ = Fᴴ * ((1 / 2 : ℂ) • (Y + Yᴴ)) * F := by
          rw [e1]
          nth_rw 1 [← hY]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  have hptσ : pt σ = F'ᴴ * ((1 / 2 : ℂ) • (Y' + Y'ᴴ)) * F' := by
    have hptH : (pt σ)ᴴ = pt σ := by rw [← pt_conjTranspose, hσH]
    have e1 : (pt σ)ᴴ = F'ᴴ * Y'ᴴ * F' := by
      rw [← hY', conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    calc pt σ = (1 / 2 : ℂ) • (pt σ + (pt σ)ᴴ) := by rw [hptH, hhalf]
      _ = F'ᴴ * ((1 / 2 : ℂ) • (Y' + Y'ᴴ)) * F' := by
          rw [e1]
          nth_rw 1 [← hY']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  obtain ⟨ε₁, hε₁, hp₁⟩ := exists_isPSD_one_add_smul _ (hherm Y)
  obtain ⟨ε₂, hε₂, hp₂⟩ := exists_isPSD_one_add_smul _ (hherm Y')
  set ε := min ε₁ ε₂ with hε
  have hε0 : 0 < ε := lt_min hε₁ hε₂
  have key : ∀ t : ℝ, |t| ≤ ε → IsPPT (ρ + (t : ℂ) • σ) := by
    intro t ht
    have e1 : ρ + (t : ℂ) • σ = Fᴴ * (1 + (t : ℂ) • ((1 / 2 : ℂ) • (Y + Yᴴ))) * Fᴴᴴ := by
      rw [conjTranspose_conjTranspose, hF, hσF, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    have e2 : pt (ρ + (t : ℂ) • σ) =
        F'ᴴ * (1 + (t : ℂ) • ((1 / 2 : ℂ) • (Y' + Y'ᴴ))) * F'ᴴᴴ := by
      rw [conjTranspose_conjTranspose, pt_add, show pt ((t : ℂ) • σ) = (t : ℂ) • pt σ from rfl, hF',
        hptσ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact isPSD_conj (hp₁ t (ht.trans (min_le_left _ _))) _
    · rw [e2]
      exact isPSD_conj (hp₂ t (ht.trans (min_le_right _ _))) _
  have hp := key ε (by rw [abs_of_pos hε0])
  have hm := key (-ε) (by rw [abs_neg, abs_of_pos hε0])
  have hsum : ρ = (1 / 2 : ℝ) • (ρ + (ε : ℂ) • σ) + (1 / 2 : ℝ) • (ρ + ((-ε : ℝ) : ℂ) • σ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  obtain ⟨c, hc⟩ := hρ.2 _ _ (isPPT_smul hp (by norm_num)) (isPPT_smul hm (by norm_num)) hsum
  apply hσρ ((2 * c - 1) / ε)
  ext i j
  have := congrFun (congrFun hc i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul] at this ⊢
  have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε0.ne'
  push_cast at this ⊢
  field_simp
  linear_combination 2 * this

end ChainWoronowicz

end

end -- public section

#print axioms ChainWoronowicz.extreme_rank_bound
