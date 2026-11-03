module

public import ThreeCopyQutritWerner.TwoCutMain

@[expose] public section


/-!
# Interior minimizers: reduction to a two-plane of product vectors

Manuscript Section 3.1.  For a complex matrix `C` of rank at most two with `N = 1`:

* `R(C) = 0` forces `C = z (e₀ e₀† + e₁ e₁†)` for an orthonormal pair `e₀, e₁` and
  `|z|² = 1/2` (eq. (10));
* `S(C) = 0` then forces `e₀`, `e₁` to be fully product vectors and `e₀ + e₁` to be a
  product vector across the cuts `1 | 23` and `2 | 13` (eq. (11)).
-/

noncomputable section

open scoped ComplexConjugate Matrix

namespace ThreeCopyQutritWerner

section Vectors

variable {ι : Type*} [Fintype ι]

/-- Pythagoras: for a unit vector `e`, `‖g - ⟨e,g⟩ e‖² = ‖g‖² - |⟨e,g⟩|²`. -/
theorem vecNormSq_sub_proj (e g : ι → ℂ) (he : vecNormSq e = 1) :
    vecNormSq (fun y => g y - braket e g * e y) =
      vecNormSq g - Complex.normSq (braket e g) := by
  apply Complex.ofReal_injective
  have hfun : (fun y => g y - braket e g * e y) = (fun y => 1 * g y + (-braket e g) * e y) := by
    funext y
    ring
  rw [← braket_self, hfun, braket_comb, ← conj_braket e g, braket_self e, he, braket_self g]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_one, map_neg]
  ring

theorem normSq_add_add_normSq_sub (z w : ℂ) :
    Complex.normSq (z + w) + Complex.normSq (z - w) =
      2 * Complex.normSq z + 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  ring

end Vectors

/-- Manuscript eq. (10), generic form: a complex matrix of rank at most two with
`‖C‖_F² = 1` and `|Tr C|² = 2` is `z (e₀ e₀† + e₁ e₁†)` for an orthonormal pair and
`|z|² = 1/2`. -/
theorem eq_smul_proj_of_normSq_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (hC : C.rank ≤ 2) (hN : frobSq C = 1)
    (hT : Complex.normSq C.trace = 2) :
    ∃ (e₀ e₁ : ι → ℂ) (z : ℂ), vecNormSq e₀ = 1 ∧ vecNormSq e₁ = 1 ∧ braket e₀ e₁ = 0 ∧
      Complex.normSq z = 1 / 2 ∧ C = z • (ketBra e₀ e₀ + ketBra e₁ e₁) := by
  have hrank : C.rank = 2 := by
    by_contra hne
    have h1 : C.rank ≤ 1 := by omega
    have h := normSq_trace_le_mul_of_rank_le C 1 h1
    have hF : ∑ i, ∑ j, Complex.normSq (C i j) = 1 := hN
    rw [hF] at h
    push_cast at h
    linarith
  obtain ⟨d, U, B, hd, hU, hCUB⟩ := exists_orthonormal_mul C
  have hd2 : d = 2 := hd.trans hrank
  subst hd2
  set e : Fin 2 → ι → ℂ := fun k x => U x k with he_def
  set g : Fin 2 → ι → ℂ := fun k y => conj (B k y) with hg_def
  have hCk : C = ketBra (e 0) (g 0) + ketBra (e 1) (g 1) := by
    ext x y
    rw [hCUB]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, ketBra, he_def, hg_def,
      Complex.conj_conj]
  have horth : ∀ j k : Fin 2, braket (e j) (e k) = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
    intro j k
    rw [← hU]
    simp only [braket, Matrix.mul_apply, Matrix.conjTranspose_apply, he_def]
    rfl
  have hunit : ∀ k : Fin 2, vecNormSq (e k) = 1 := by
    intro k
    apply Complex.ofReal_injective
    rw [← braket_self, horth k k, Matrix.one_apply_eq, Complex.ofReal_one]
  have h01 : braket (e 0) (e 1) = 0 := by
    rw [horth 0 1, Matrix.one_apply_ne (by decide)]
  -- `N` and `Tr C` in terms of the right factors
  have hNg : frobSq C = vecNormSq (g 0) + vecNormSq (g 1) := by
    rw [hCk, frobSq_add, frobSq_ketBra_vecNormSq, frobSq_ketBra_vecNormSq, hsInner_ketBra, h01,
      zero_mul, Complex.zero_re, hunit 0, hunit 1]
    ring
  have hTg : C.trace = braket (g 0) (e 0) + braket (g 1) (e 1) := by
    rw [hCk, Matrix.trace_add, trace_ketBra, trace_ketBra]
  set β₀ := braket (e 0) (g 0) with hβ₀
  set β₁ := braket (e 1) (g 1) with hβ₁
  have hT' : Complex.normSq (β₀ + β₁) = 2 := by
    rw [← hT, hTg, ← conj_braket (e 0) (g 0), ← conj_braket (e 1) (g 1), ← map_add,
      Complex.normSq_conj]
  have hp0 := vecNormSq_sub_proj (e 0) (g 0) (hunit 0)
  have hp1 := vecNormSq_sub_proj (e 1) (g 1) (hunit 1)
  have hn0 := vecNormSq_nonneg (fun y => g 0 y - braket (e 0) (g 0) * e 0 y)
  have hn1 := vecNormSq_nonneg (fun y => g 1 y - braket (e 1) (g 1) * e 1 y)
  have hpar := normSq_add_add_normSq_sub β₀ β₁
  have hq := Complex.normSq_nonneg (β₀ - β₁)
  rw [hN] at hNg
  have hz0 : vecNormSq (fun y => g 0 y - braket (e 0) (g 0) * e 0 y) = 0 := by
    rw [← hβ₀] at hp0 hn0 ⊢
    linarith
  have hz1 : vecNormSq (fun y => g 1 y - braket (e 1) (g 1) * e 1 y) = 0 := by
    rw [← hβ₁] at hp1 hn1 ⊢
    linarith
  have hqz : Complex.normSq (β₀ - β₁) = 0 := by
    rw [← hβ₀] at hp0 hn0
    rw [← hβ₁] at hp1 hn1
    linarith
  have hββ : β₁ = β₀ := (sub_eq_zero.mp (Complex.normSq_eq_zero.mp hqz)).symm
  have hg0 : ∀ y, g 0 y = β₀ * e 0 y := fun y =>
    sub_eq_zero.mp (eq_zero_of_vecNormSq_eq_zero _ hz0 y)
  have hg1 : ∀ y, g 1 y = β₀ * e 1 y := fun y => by
    rw [← hββ]
    exact sub_eq_zero.mp (eq_zero_of_vecNormSq_eq_zero _ hz1 y)
  refine ⟨e 0, e 1, conj β₀, hunit 0, hunit 1, h01, ?_, ?_⟩
  · rw [Complex.normSq_conj]
    have h2 : Complex.normSq (β₀ + β₁) = 4 * Complex.normSq β₀ := by
      rw [hββ, ← two_mul, Complex.normSq_mul]
      norm_num [Complex.normSq_apply]
    linarith
  · ext x y
    rw [hCk]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ketBra, hg0, hg1, map_mul]
    ring

/-- Manuscript eq. (10): a matrix of rank at most two with `N = 1` and `R = 0`. -/
theorem eq_smul_proj_of_formR_eq_zero {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) (hN : invN C = 1)
    (hR : formR C = 0) :
    ∃ (e₀ e₁ : a × b × c → ℂ) (z : ℂ), vecNormSq e₀ = 1 ∧ vecNormSq e₁ = 1 ∧
      braket e₀ e₁ = 0 ∧ Complex.normSq z = 1 / 2 ∧ C = z • (ketBra e₀ e₀ + ketBra e₁ e₁) := by
  refine eq_smul_proj_of_normSq_trace C hC hN ?_
  unfold formR at hR
  unfold invT at hR
  rw [hN] at hR
  linarith

section Cuts

variable {L R : Type*} [Fintype L] [Fintype R]

theorem ptraceL_smul (z : ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    ptraceL (z • X) = z • ptraceL X := by
  ext k k'
  simp only [ptraceL, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptraceR_smul (z : ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    ptraceR (z • X) = z • ptraceR X := by
  ext j j'
  simp only [ptraceR, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The two-factor form is homogeneous of degree two. -/
theorem cutForm_smul (z : ℂ) (X : Matrix (L × R) (L × R) ℂ) :
    cutForm (z • X) = Complex.normSq z * cutForm X := by
  unfold cutForm
  rw [ptraceL_smul, ptraceR_smul, frobSq_smul, frobSq_smul, frobSq_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.normSq_mul]
  ring

/-- Eq. (11): if the two-factor form vanishes on `x₀ x₀† + x₁ x₁†` for an orthonormal pair,
the three defects `e(x₀,x₀)`, `e(x₁,x₁)`, `e(x₁,x₀)` vanish. -/
theorem biDefect_eq_zero_of_cutForm_proj (x₀ x₁ : L × R → ℂ) (h0 : vecNormSq x₀ = 1)
    (h1 : vecNormSq x₁ = 1) (h01 : braket x₀ x₁ = 0)
    (hQ : cutForm (ketBra x₀ x₀ + ketBra x₁ x₁) = 0) :
    biDefect x₀ x₀ = 0 ∧ biDefect x₁ x₁ = 0 ∧ biDefect x₁ x₀ = 0 := by
  have hτ0 : braket x₀ x₀ = 1 := by rw [braket_self, h0, Complex.ofReal_one]
  have hτ1 : braket x₁ x₁ = 1 := by rw [braket_self, h1, Complex.ofReal_one]
  have key := cutForm_ketBra_add x₀ x₁ x₀ x₁ 1 1 0 1 h0 h0 h1 h1 h01 h01 hτ0 hτ1
  rw [hQ, Complex.normSq_zero] at key
  have e1 := biDefect_nonneg x₀ x₀
  have e2 := biDefect_nonneg x₁ x₁
  have e3 := biDefect_nonneg x₁ x₀
  have e5 := ptraceNormSq_nonneg (ketBra x₁ x₀ - ketBra x₁ x₀)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Vanishing defect forces the bi-antisymmetric part to vanish pointwise. -/
theorem biAnti_eq_zero_of_biDefect_eq_zero (u v : L × R → ℂ) (h : biDefect u v = 0)
    (p : (L × R) × (L × R)) : biAnti u v p = 0 := by
  have h4 := four_mul_biDefect u v
  rw [h, mul_zero] at h4
  have hs := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => Complex.normSq_nonneg (biAnti u v q))).mp h4.symm p (Finset.mem_univ p)
  exact Complex.normSq_eq_zero.mp hs

end Cuts

section Product

variable {L R : Type*}

theorem biAnti_comm (u v : L × R → ℂ) : biAnti u v = biAnti v u := by
  funext p
  simp only [biAnti]
  ring

theorem biAnti_add_self (u v : L × R → ℂ) (p : (L × R) × (L × R)) :
    biAnti (fun x => u x + v x) (fun x => u x + v x) p =
      biAnti u u p + biAnti v v p + 2 * biAnti v u p := by
  simp only [biAnti]
  ring

theorem biAnti_self_apply (w : L × R → ℂ) (l l' : L) (r r' : R) :
    biAnti w w ((l, r), (l', r')) = 2 * (w (l, r) * w (l', r') - w (l', r) * w (l, r')) := by
  simp only [biAnti]
  ring

/-- A two-index array with all `2 × 2` minors zero is a product. -/
theorem exists_product_of_minors (w : L × R → ℂ)
    (h : ∀ l l' r r', w (l, r) * w (l', r') = w (l', r) * w (l, r')) :
    ∃ (α : L → ℂ) (β : R → ℂ), ∀ l r, w (l, r) = α l * β r := by
  by_cases hw : ∃ l r, w (l, r) ≠ 0
  · obtain ⟨l₀, r₀, h₀⟩ := hw
    refine ⟨fun l => w (l, r₀), fun r => w (l₀, r) / w (l₀, r₀), fun l r => ?_⟩
    show w (l, r) = w (l, r₀) * (w (l₀, r) / w (l₀, r₀))
    rw [mul_div_assoc', eq_div_iff h₀]
    linear_combination h l l₀ r r₀
  · push_neg at hw
    exact ⟨fun _ => 0, fun _ => 0, fun l r => by simp [hw l r]⟩

/-- A vector whose bi-antisymmetric part vanishes is a product vector across the cut. -/
theorem exists_product_of_biAnti_self_eq_zero (w : L × R → ℂ)
    (h : ∀ p, biAnti w w p = 0) : ∃ (α : L → ℂ) (β : R → ℂ), ∀ l r, w (l, r) = α l * β r := by
  apply exists_product_of_minors
  intro l l' r r'
  have h2 := h ((l, r), (l', r'))
  rw [biAnti_self_apply] at h2
  linear_combination h2 / 2

/-- Product across `1 | 23` and across `2 | 13` gives a fully product vector. -/
theorem exists_full_product {a b c : Type*} (w : a × b × c → ℂ)
    (h1 : ∃ (α : a → ℂ) (β : b × c → ℂ), ∀ i j k, w (i, j, k) = α i * β (j, k))
    (h2 : ∃ (α : b → ℂ) (β : a × c → ℂ), ∀ i j k, w (i, j, k) = α j * β (i, k)) :
    ∃ (u₁ : a → ℂ) (u₂ : b → ℂ) (u₃ : c → ℂ), ∀ i j k, w (i, j, k) = u₁ i * u₂ j * u₃ k := by
  obtain ⟨α₁, β₁, hw1⟩ := h1
  obtain ⟨α₂, β₂, hw2⟩ := h2
  by_cases hw : ∃ i j k, w (i, j, k) ≠ 0
  · obtain ⟨i₀, j₀, k₀, h₀⟩ := hw
    have hα : α₁ i₀ ≠ 0 := by
      intro h
      apply h₀
      rw [hw1, h, zero_mul]
    refine ⟨α₁, α₂, fun k => β₂ (i₀, k) / α₁ i₀, fun i j k => ?_⟩
    show w (i, j, k) = α₁ i * α₂ j * (β₂ (i₀, k) / α₁ i₀)
    have e2 : α₁ i₀ * β₁ (j, k) = α₂ j * β₂ (i₀, k) := by rw [← hw1, hw2]
    rw [hw1, mul_div_assoc', eq_div_iff hα]
    linear_combination (α₁ i) * e2
  · push_neg at hw
    exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun i j k => by simp [hw i j k]⟩

end Product

section Plane

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

theorem vecNormSq_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : κ ≃ ι) (u : ι → ℂ) :
    vecNormSq (fun q => u (σ q)) = vecNormSq u := by
  unfold vecNormSq
  exact Fintype.sum_equiv σ (fun q => Complex.normSq (u (σ q))) (fun x => Complex.normSq (u x))
    (fun _ => rfl)

theorem braket_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : κ ≃ ι) (u v : ι → ℂ) :
    braket (fun q => u (σ q)) (fun q => v (σ q)) = braket u v := by
  unfold braket
  exact Fintype.sum_equiv σ (fun q => conj (u (σ q)) * v (σ q)) (fun x => conj (u x) * v x)
    (fun _ => rfl)

theorem submatrix_ketBra_add {ι κ : Type*} (σ : κ ≃ ι) (u v : ι → ℂ) :
    (ketBra u u + ketBra v v).submatrix σ σ =
      ketBra (fun q => u (σ q)) (fun q => u (σ q)) + ketBra (fun q => v (σ q)) (fun q => v (σ q)) := by
  ext x y
  rfl

/-- The vectors of a two-plane on which the cut forms `Q₁`, `Q₂` vanish satisfy the
hypotheses of the two-plane lemma: both basis vectors are fully product and their sum is
a product vector across `1 | 23` and `2 | 13`. -/
theorem plane_products_of_cutForms_eq_zero (e₀ e₁ : a × b × c → ℂ) (h0 : vecNormSq e₀ = 1)
    (h1 : vecNormSq e₁ = 1) (h01 : braket e₀ e₁ = 0)
    (hQ₁ : cutForm (ketBra e₀ e₀ + ketBra e₁ e₁) = 0)
    (hQ₂ : cutForm ((ketBra e₀ e₀ + ketBra e₁ e₁).submatrix siteEquiv₂ siteEquiv₂) = 0) :
    (∃ (u₁ : a → ℂ) (u₂ : b → ℂ) (u₃ : c → ℂ), ∀ i j k, e₀ (i, j, k) = u₁ i * u₂ j * u₃ k) ∧
    (∃ (u₁ : a → ℂ) (u₂ : b → ℂ) (u₃ : c → ℂ), ∀ i j k, e₁ (i, j, k) = u₁ i * u₂ j * u₃ k) ∧
    (∃ (α : a → ℂ) (β : b × c → ℂ), ∀ i j k, e₀ (i, j, k) + e₁ (i, j, k) = α i * β (j, k)) ∧
    (∃ (α : b → ℂ) (β : a × c → ℂ), ∀ i j k, e₀ (i, j, k) + e₁ (i, j, k) = α j * β (i, k)) := by
  -- cut `1 | 23`
  obtain ⟨d00, d11, d10⟩ := biDefect_eq_zero_of_cutForm_proj e₀ e₁ h0 h1 h01 hQ₁
  -- cut `2 | 13`
  set f₀ : b × a × c → ℂ := fun q => e₀ (siteEquiv₂ q) with hf₀
  set f₁ : b × a × c → ℂ := fun q => e₁ (siteEquiv₂ q) with hf₁
  rw [submatrix_ketBra_add] at hQ₂
  obtain ⟨g00, g11, g10⟩ := biDefect_eq_zero_of_cutForm_proj f₀ f₁
    (by rw [hf₀, vecNormSq_comp_equiv, h0]) (by rw [hf₁, vecNormSq_comp_equiv, h1])
    (by rw [hf₀, hf₁, braket_comp_equiv, h01]) hQ₂
  -- products across each cut
  have cut1 : ∀ w : a × b × c → ℂ, (∀ p, biAnti w w p = 0) →
      ∃ (α : a → ℂ) (β : b × c → ℂ), ∀ i j k, w (i, j, k) = α i * β (j, k) := by
    intro w hw
    obtain ⟨α, β, h⟩ := exists_product_of_biAnti_self_eq_zero w hw
    exact ⟨α, β, fun i j k => h i (j, k)⟩
  have cut2 : ∀ w : a × b × c → ℂ, (∀ p, biAnti (fun q : b × a × c => w (siteEquiv₂ q))
      (fun q : b × a × c => w (siteEquiv₂ q)) p = 0) →
      ∃ (α : b → ℂ) (β : a × c → ℂ), ∀ i j k, w (i, j, k) = α j * β (i, k) := by
    intro w hw
    obtain ⟨α, β, h⟩ := exists_product_of_biAnti_self_eq_zero _ hw
    exact ⟨α, β, fun i j k => h j (i, k)⟩
  have s1 : ∀ p, biAnti (fun x => e₀ x + e₁ x) (fun x => e₀ x + e₁ x) p = 0 := by
    intro p
    rw [biAnti_add_self, biAnti_eq_zero_of_biDefect_eq_zero _ _ d00,
      biAnti_eq_zero_of_biDefect_eq_zero _ _ d11, biAnti_eq_zero_of_biDefect_eq_zero _ _ d10]
    ring
  have s2 : ∀ p, biAnti (fun q : b × a × c => e₀ (siteEquiv₂ q) + e₁ (siteEquiv₂ q))
      (fun q : b × a × c => e₀ (siteEquiv₂ q) + e₁ (siteEquiv₂ q)) p = 0 := by
    intro p
    have := biAnti_add_self f₀ f₁ p
    rw [biAnti_eq_zero_of_biDefect_eq_zero _ _ g00, biAnti_eq_zero_of_biDefect_eq_zero _ _ g11,
      biAnti_eq_zero_of_biDefect_eq_zero _ _ g10] at this
    rw [hf₀, hf₁] at this
    rw [this]
    ring
  refine ⟨exists_full_product e₀ (cut1 e₀ (biAnti_eq_zero_of_biDefect_eq_zero _ _ d00))
      (cut2 e₀ (biAnti_eq_zero_of_biDefect_eq_zero _ _ g00)),
    exists_full_product e₁ (cut1 e₁ (biAnti_eq_zero_of_biDefect_eq_zero _ _ d11))
      (cut2 e₁ (biAnti_eq_zero_of_biDefect_eq_zero _ _ g11)), ?_, ?_⟩
  · exact cut1 (fun x => e₀ x + e₁ x) s1
  · exact cut2 (fun x => e₀ x + e₁ x) s2

end Plane

end ThreeCopyQutritWerner

end
