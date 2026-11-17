module

public import FormalResearch.Special.DiscreteAiryKappaOrderSetup
public import FormalResearch.Special.DiscreteAiryKappaChart

/-!
# Order-sharp `κ`: the data bundle and the two bounds (plan K1, assembly, abstract part)

`KkData` collects, for the natural-gauge `3j` chain `Y = Ŷ` at a node (`δ³ = 1/N`) and the chart sequences `X_k = X(q_k)`, `g_k = g(q_k)`, exactly the facts the
mass accounting uses (window positions, lattice gaps, `g_min ≤ g ≤ g_max`, the pointwise Airy matching with `μ`, the left bound, the monotone decay, the Gauss
weight as finite-sum inequalities).  `KkSmall` collects the positivity and smallness conditions on `δ`.  Then

* `kk_rest_all`: an index `k₁` with `X_{k₁} ≤ 1/δ < X_{k₁+1}` and `|Y_k - κ g_k Ai(X_k)| ≤ (C+1)δ³|κ|` for `J ≤ k ≤ k₁ + 1`;
* `kk_upper`: `κ² δ ≤ 80 c₂/(g_min² σ₀)`;
* `kk_lower`: `1 ≤ Q κ² δ` (`Q = kkQ ...`).

**Claim class: proved** (abstract; `DiscreteAiryKappaOrder` supplies the data for the actual chain).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- The facts about the chain `Y`, the chart sequences `X, g`, and `κ, μ` used by the mass accounting. -/
structure KkData (Y X g : ℤ → ℝ) (Nz : ℤ) (δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ : ℝ) (J m Nw : ℤ) : Prop where
  hNz : (Nz : ℝ) = 1 / δ ^ 3
  hNz1 : 1 ≤ Nz
  hq1 : qs < 1
  p1 : qs - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3
  p2 : ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - r + δ ^ 3
  p3 : qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3
  p4 : ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3
  hJ : 1 ≤ J
  hJm : J ≤ m
  hm1 : m + 1 ≤ Nw
  gap : ∀ k ∈ Finset.Icc J Nw, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ
  Xm : ∀ k ∈ Finset.Icc J (m + 1), X k ≤ 1 / 4
  X0 : 0 ≤ X m ∧ X m ≤ c2 * δ
  XN : c1 * (r / 4) / δ ^ 2 ≤ X Nw
  gup : ∀ k ∈ Finset.Icc J (Nw + 1), |g k| ≤ gmax
  glo : ∀ k ∈ Finset.Icc J (Nw + 1), gmin ≤ g k
  pt : ∀ k ∈ Finset.Icc J (Nw + 1), |Y k - (κ * (g k * airyAi (X k)) + μ * (g k * airyBi (X k)))| ≤
    C * δ ^ 3 * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k))
  mu : |μ| ≤ Cmu * Real.sqrt (Nz : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ
  kap : κmin ≤ |κ|
  left : ∀ k : ℤ, k ≤ J + 1 → Y k ^ 2 ≤ Cl * (Y (J + 1) ^ 2 + Y J ^ 2)
  mono : ∀ m' : ℤ, qs ≤ ((m' : ℝ) + 1 / 2) * δ ^ 3 → ∀ k : ℤ, m' + 1 ≤ k → Y k ^ 2 ≤ Y (m' + 1) ^ 2
  sum : ∀ (ka : ℤ) (n' : ℕ), ∑ i ∈ range n', Y (ka + (i : ℤ)) ^ 2 ≤ 1 / δ ^ 3
  cover : ∀ S : Finset ℤ, (∀ k : ℤ, 0 ≤ k → k < Nz → k ∈ S) → 1 / δ ^ 3 ≤ ∑ k ∈ S, Y k ^ 2

/-- Positivity and smallness conditions on `δ` (`σ₀ = min(√(3c₁r/4), 1/(20c₂))`, `B₀ = (450 g_max + C) C_mu`). -/
structure KkSmall (δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0 : ℝ) : Prop where
  hδ : 0 < δ
  hr : 0 < r
  hC : 0 < C
  hCmu : 0 < Cmu
  hξ0 : 0 < ξ0
  hgmin : 0 < gmin
  hgg : gmin ≤ gmax
  hc1 : 0 < c1
  hc12 : c1 ≤ c2
  hκmin : 0 < κmin
  hσ0 : σ0 = min (√(3 * c1 * r / 4)) (1 / (20 * c2))
  d1 : δ ≤ 1 / 2
  d2 : δ ≤ c1 * r / (8 * (c2 + 1))
  d3 : δ ≤ σ0 / 100
  d4 : δ ≤ gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2)
  d5 : δ ≤ σ0 ^ 2 / 2
  d6 : δ ≤ ξ0 / 14
  d7 : δ ≤ κmin * ξ0 ^ 3 / (48 * ((450 * gmax + C) * Cmu + 1))
  d8 : δ ^ 3 ≤ r / 8

lemma KkSmall.sigma_pos {δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0 : ℝ} (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) :
    0 < σ0 := by
  have hc2 : 0 < c2 := lt_of_lt_of_le s.hc1 s.hc12
  rw [s.hσ0]
  exact lt_min (Real.sqrt_pos.2 (by have := s.hr; have := s.hc1; positivity)) (by positivity)

/-- Common consequences of `KkSmall`. -/
lemma KkSmall.c2δ {δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0 : ℝ} (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) :
    c2 * δ ≤ 1 / 2000 := by
  have hc2 : 0 < c2 := lt_of_lt_of_le s.hc1 s.hc12
  have h1 : c2 * δ ≤ c2 * (σ0 / 100) := mul_le_mul_of_nonneg_left s.d3 hc2.le
  have h2 : σ0 ≤ 1 / (20 * c2) := s.hσ0 ▸ min_le_right _ _
  have h3 : c2 * σ0 ≤ 1 / 20 := by
    calc c2 * σ0 ≤ c2 * (1 / (20 * c2)) := mul_le_mul_of_nonneg_left h2 hc2.le
      _ = 1 / 20 := by field_simp
  nlinarith

/-- **The remainder bound on the extended window** and the index `k₁` with `X_{k₁} ≤ 1/δ < X_{k₁+1}`. -/
lemma kk_rest_all {Y X g : ℤ → ℝ} {Nz J m Nw : ℤ} {δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ σ0 : ℝ}
    (d : KkData Y X g Nz δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw)
    (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) :
    ∃ k1 : ℤ, m + 1 ≤ k1 ∧ k1 + 1 ≤ Nw ∧ X k1 ≤ 1 / δ ∧ 1 / δ < X (k1 + 1) ∧
      ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ| := by
  have hδp := s.hδ
  have hδ1' : δ ≤ 1 := by linarith [s.d1]
  have hc2 : 0 < c2 := lt_of_lt_of_le s.hc1 s.hc12
  have hδ3pos : 0 < δ ^ 3 := pow_pos hδp 3
  have hgmax : 0 < gmax := lt_of_lt_of_le s.hgmin s.hgg
  set B0 : ℝ := (450 * gmax + C) * Cmu with hB0def
  have hB0 : 0 ≤ B0 := by have := s.hC; have := s.hCmu; positivity
  -- smallness of μ
  have hNδ : 1 / δ ^ 3 = (Nz : ℝ) := d.hNz.symm
  have hμb : |μ| ≤ Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) := by
    have hN1 : (1 : ℝ) ≤ Nz := by exact_mod_cast d.hNz1
    have hsq : Real.sqrt (Nz : ℝ) ≤ 1 / δ ^ 3 := by
      rw [hNδ]; exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    refine d.mu.trans ?_
    have h0 : 0 ≤ Real.exp (-ξ0 / δ ^ 3) / δ := by positivity
    calc Cmu * Real.sqrt (Nz : ℝ) * Real.exp (-ξ0 / δ ^ 3) / δ = Cmu * Real.sqrt (Nz : ℝ) * (Real.exp (-ξ0 / δ ^ 3) / δ) := by ring
      _ ≤ Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq s.hCmu.le) h0
  have hμE : (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) ≤ δ ^ 3 * |κ| := by
    have hsm := kk_mu_small hδp hδ1' s.hξ0 hB0 s.d6 s.d7
    have h1' : (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) ≤
        (450 * gmax + C) * (Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ)) * Real.exp (7 / δ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμb (by have := s.hC; positivity)) (Real.exp_pos _).le
    have e1 : (450 * gmax + C) * (Cmu * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ)) * Real.exp (7 / δ ^ 2) =
        B0 * (1 / δ ^ 3) * (Real.exp (-ξ0 / δ ^ 3) / δ) * Real.exp (7 / δ ^ 2) := by rw [hB0def]; ring
    rw [e1] at h1'
    nlinarith [mul_le_mul_of_nonneg_left d.kap hδ3pos.le]
  -- the index k₁
  have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδp]; linarith
  have hδc4 : δ < c1 * r / 4 := by
    have h1 : c1 * r / (8 * (c2 + 1)) ≤ c1 * r / 8 := by
      apply div_le_div_of_nonneg_left (by have := s.hc1; have := s.hr; positivity) (by norm_num) (by linarith)
    have h2 : 0 < c1 * r / 8 := by have := s.hc1; have := s.hr; positivity
    linarith [s.d2]
  have hXNge : 1 / δ < X Nw := by
    have h1 : 1 / δ = δ / δ ^ 2 := by field_simp
    have h2 : c1 * (r / 4) / δ ^ 2 = (c1 * r / 4) / δ ^ 2 := by ring
    have h3 : δ / δ ^ 2 < (c1 * r / 4) / δ ^ 2 := div_lt_div_of_pos_right hδc4 (by positivity)
    have := d.XN
    linarith
  have hX1m : X (m + 1) ≤ 1 / 4 := d.Xm (m + 1) (Finset.mem_Icc.2 ⟨by have := d.hJm; omega, le_rfl⟩)
  obtain ⟨k1, hk11, hk12, hk13, hk14⟩ := kk_ivt (X := X) (J := m + 1) (b := Nw) (t := 1 / δ)
    (by linarith) hXNge d.hm1
  refine ⟨k1, hk11, by omega, hk13, hk14, ?_⟩
  have hmonoX : ∀ k ∈ Finset.Icc J Nw, X k ≤ X (k + 1) := fun k hk => by
    have h0 : 0 ≤ c1 * δ := by have := s.hc1; positivity
    linarith [(d.gap k hk).1]
  have hXk1 : X (k1 + 1) ≤ 1 / δ + 1 / 2 := by
    have := (d.gap k1 (Finset.mem_Icc.2 ⟨by have := d.hJm; omega, by omega⟩)).2
    have := s.c2δ
    linarith
  have hXle : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → X k ≤ 2 / δ := by
    intro k hk1' hk2'
    have := kc_mono hmonoX k (k1 + 1) hk1' hk2' (by omega)
    have e : 2 / δ = 1 / δ + 1 / δ := by ring
    linarith
  intro k hk1' hk2'
  have hkmem : k ∈ Finset.Icc J (Nw + 1) := Finset.mem_Icc.2 ⟨hk1', by omega⟩
  exact kk_rest s.hC.le hδp hδ1' hgmax.le (d.pt k hkmem) (d.gup k hkmem) (airyWt_le_one _)
    (kk_biwt_le hδp hδ1' (hXle k hk1' hk2')) (airyBiWt_pos _).le (apx_airyBi_global (X k)).1 hμE

/-- **Upper bound** `κ² δ ≤ 80 c₂/(g_min² σ₀)`. -/
lemma kk_upper {Y X g : ℤ → ℝ} {Nz J m Nw : ℤ} {δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ σ0 : ℝ}
    (d : KkData Y X g Nz δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw)
    (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ m → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|) :
    κ ^ 2 * δ ≤ 80 * c2 / (gmin ^ 2 * σ0) := by
  have hδp := s.hδ
  have hδ1' : δ ≤ 1 := by linarith [s.d1]
  have hc2 : 0 < c2 := lt_of_lt_of_le s.hc1 s.hc12
  have hδ3pos : 0 < δ ^ 3 := pow_pos hδp 3
  have hσ0p := s.sigma_pos
  have hJm := d.hJm
  have hgapZ : ∀ k : ℤ, J ≤ k → k < m → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ :=
    fun k h1 h2 => d.gap k (Finset.mem_Icc.2 ⟨h1, by have := d.hm1; omega⟩)
  have hpos : r - δ ^ 3 ≤ ((m - J : ℤ) : ℝ) * δ ^ 3 := by
    have e : ((m - J : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + 1 / 2) * δ ^ 3 - ((J : ℝ) + 1 / 2) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith [d.p3, d.p2]
  have hδc' : c2 * δ ^ 3 ≤ c1 * r / 8 := by
    have h0 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ, pow_pos hδp 2]
    have h1 : c2 * δ ^ 3 ≤ c2 * δ := mul_le_mul_of_nonneg_left h0 hc2.le
    have h2 : c2 * δ ≤ c2 * (c1 * r / (8 * (c2 + 1))) := mul_le_mul_of_nonneg_left s.d2 hc2.le
    have h3 : c2 * (c1 * r / (8 * (c2 + 1))) ≤ c1 * r / 8 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos s.hc1 s.hr]
    linarith
  have hδ5' : δ ^ 5 ≤ gmin ^ 2 * c1 / (80 * c2 * σ0 * (C + 1) ^ 2) := by
    have h0 : δ ^ 5 ≤ δ := by
      have : δ ^ 4 ≤ 1 := pow_le_one₀ hδp.le hδ1'
      nlinarith [pow_pos hδp 4]
    linarith [s.d4]
  have hmassUB : ∀ (ka : ℤ) (n' : ℕ), ∑ i ∈ range n', Y (ka + (i : ℤ)) ^ 2 ≤ 1 / δ ^ 3 := d.sum
  exact kk_ub_final (X := X) (Y := Y) (g := g) (J := J) (m := m) (δ := δ) (c1 := c1) (c2 := c2)
    (r := r) (gmin := gmin) (C := C) (κ := κ) (σ0 := σ0) hJm hδp s.hc1 s.hc12 s.hr s.hgmin s.hC s.hσ0 s.d8 hδc'
    (by linarith [s.d3]) hδ5' hgapZ d.X0 hpos
    (fun k h1 h2 => d.glo k (Finset.mem_Icc.2 ⟨h1, by have := d.hm1; omega⟩)) hrest hmassUB

/-- **Lower bound** `1 ≤ Q κ² δ`. -/
lemma kk_lower {Y X g : ℤ → ℝ} {Nz J m Nw : ℤ} {δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ σ0 : ℝ}
    (d : KkData Y X g Nz δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw)
    (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) (hCl : 0 ≤ Cl) {k1 : ℤ} (hk1 : m + 1 ≤ k1) (hk1N : k1 + 1 ≤ Nw)
    (hX1 : X k1 ≤ 1 / δ) (hX2 : 1 / δ < X (k1 + 1))
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|) :
    1 ≤ kkQ c1 c2 gmax C σ0 (c2 * (r + 1)) (r + 3) Cl * (κ ^ 2 * δ) := by
  have hδp := s.hδ
  have hδ1' : δ ≤ 1 := by linarith [s.d1]
  have hc2 : 0 < c2 := lt_of_lt_of_le s.hc1 s.hc12
  have hδ3pos : 0 < δ ^ 3 := pow_pos hδp 3
  have hσ0p := s.sigma_pos
  have hJm := d.hJm
  have hgmax : 0 < gmax := lt_of_lt_of_le s.hgmin s.hgg
  have hgapZ : ∀ k : ℤ, J ≤ k → k < Nw → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ :=
    fun k h1 h2 => d.gap k (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  have hpos : r - δ ^ 3 ≤ ((m - J : ℤ) : ℝ) * δ ^ 3 := by
    have e : ((m - J : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + 1 / 2) * δ ^ 3 - ((J : ℝ) + 1 / 2) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith [d.p3, d.p2]
  have hposU : ((m - J : ℤ) : ℝ) * δ ^ 3 < r + δ ^ 3 := by
    have e : ((m - J : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + 1 / 2) * δ ^ 3 - ((J : ℝ) + 1 / 2) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith [d.p4, d.p1]
  have hδc' : c2 * δ ^ 3 ≤ c1 * r / 8 := by
    have h0 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ, pow_pos hδp 2]
    have h1 : c2 * δ ^ 3 ≤ c2 * δ := mul_le_mul_of_nonneg_left h0 hc2.le
    have h2 : c2 * δ ≤ c2 * (c1 * r / (8 * (c2 + 1))) := mul_le_mul_of_nonneg_left s.d2 hc2.le
    have h3 : c2 * (c1 * r / (8 * (c2 + 1))) ≤ c1 * r / 8 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos s.hc1 s.hr]
    linarith
  have hσ2 : σ0 ^ 2 ≤ 3 * c1 * r / 4 := by
    have h := min_le_left (√(3 * c1 * r / 4)) (1 / (20 * c2))
    rw [← s.hσ0] at h
    calc σ0 ^ 2 ≤ √(3 * c1 * r / 4) ^ 2 := pow_le_pow_left₀ hσ0p.le h 2
      _ = 3 * c1 * r / 4 := Real.sq_sqrt (by have := s.hc1; have := s.hr; positivity)
  have hXJ := kk_xJ (X := X) (J := J) (m := m) (δ := δ) (c1 := c1) (c2 := c2) (r := r) (σ0 := σ0) hJm hδp s.hc1 hσ2 s.d8 hδc'
    (fun k h1 h2 => (hgapZ k h1 (by have := d.hm1; omega)).1) d.X0.2 hpos
  have hs : 2 * δ ^ 2 ≤ σ0 ^ 2 := by
    have : δ ^ 2 ≤ δ := by nlinarith
    linarith [s.d5]
  have hXJlow : -X J ≤ c2 * (r + 1) / δ ^ 2 := by
    have hsp := kk_span_up (X := X) (ε' := c2 * δ) hJm
      (fun k h1 h2 => (hgapZ k h1 (by have := d.hm1; omega)).2)
    have h1 : ((m - J : ℤ) : ℝ) * (c2 * δ) ≤ c2 * (r + 1) / δ ^ 2 := by
      have h2 : ((m - J : ℤ) : ℝ) ≤ (r + δ ^ 3) / δ ^ 3 := by
        rw [le_div_iff₀ hδ3pos]; linarith
      have h3 : ((m - J : ℤ) : ℝ) * (c2 * δ) ≤ (r + δ ^ 3) / δ ^ 3 * (c2 * δ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h4 : (r + δ ^ 3) / δ ^ 3 * (c2 * δ) = c2 * (r + δ ^ 3) / δ ^ 2 := by field_simp
      rw [h4] at h3
      refine h3.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [pow_le_one₀ hδp.le hδ1' (n := 3)]
    have := d.X0.1
    linarith
  have hkT : X (k1 + 1 - 1) ≤ 1 / δ ∧ 1 / δ ≤ X (k1 + 1) := ⟨by simpa using hX1, hX2.le⟩
  have hmonoT' : ∀ k : ℤ, k1 + 1 ≤ k → Y k ^ 2 ≤ Y (k1 + 1) ^ 2 := by
    intro k hk
    have := d.mono (k1 + 1 - 1)
      (by
        have : (m : ℝ) ≤ ((k1 + 1 - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : m ≤ k1 + 1 - 1)
        nlinarith [d.p3, hδ3pos]) k (by omega)
    simpa using this
  have hmassLB : 1 / δ ^ 3 ≤ ∑ k ∈ Finset.Ico 0 (k1 + 1 + Nz), Y k ^ 2 :=
    d.cover _ (fun k hk1' hk2' => Finset.mem_Ico.2 ⟨hk1', by have := d.hJ; omega⟩)
  have hJcnt : ((J + 2 : ℤ) : ℝ) ≤ 2 / δ ^ 3 := by
    have h8 : δ ^ 3 ≤ 1 / 8 := by
      have : δ ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hδp.le s.d1 3
      norm_num at this; exact this
    have e : ((J + 2 : ℤ) : ℝ) * δ ^ 3 = ((J : ℝ) + 1 / 2) * δ ^ 3 + 3 / 2 * δ ^ 3 := by push_cast; ring
    rw [le_div_iff₀ hδ3pos, e]
    nlinarith [d.p2, d.hq1, s.hr]
  have hmcnt : ((m + 2 - J : ℤ) : ℝ) ≤ (r + 3) / δ ^ 3 := by
    rw [le_div_iff₀ hδ3pos]
    have e : ((m + 2 - J : ℤ) : ℝ) * δ ^ 3 = ((m - J : ℤ) : ℝ) * δ ^ 3 + 2 * δ ^ 3 := by push_cast; ring
    rw [e]; nlinarith [pow_le_one₀ hδp.le hδ1' (n := 3)]
  have hNN : ((Nz : ℤ) : ℝ) ≤ 1 / δ ^ 3 := d.hNz.le
  exact kk_lb_final (X := X) (Y := Y) (g := g) (J := J) (m := m) (kT := k1 + 1) (NN := Nz) (δ := δ)
    (c1 := c1) (c2 := c2) (G := gmax) (C := C) (κ := κ) (s0 := σ0) (R0 := c2 * (r + 1)) (Rc := r + 3) (Cl := Cl) hδp hδ1'
    s.hc1 hc2.le hσ0p hgmax.le s.hC.le (by have := s.hr; positivity) (by have := s.hr; positivity) hCl
    (by have := d.hJ; omega) hJm (by omega) (by have := d.hNz1; omega) (by have := s.c2δ; linarith)
    (fun k h1' h2' => hgapZ k h1' (by omega)) hXJ hs hXJlow d.X0.1
    (d.Xm (m + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)) hkT hrest
    (fun k h1' h2' => d.gup k (Finset.mem_Icc.2 ⟨h1', by omega⟩)) d.left hmonoT' hmassLB hNN hJcnt hmcnt

end FormalResearch.Special
