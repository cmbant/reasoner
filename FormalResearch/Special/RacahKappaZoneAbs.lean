module

public import FormalResearch.Special.DiscreteAiryKappaSharpZone
public import FormalResearch.Special.RacahKappaMu

/-!
# The zone mass from the Airy window (abstract chart data)

`rk_zone_abs`: from the chart data and the pointwise Airy matching `Y = κ g Ai + μ g Bi + O(δ³(|κ|W + |μ|W̃))` on a window `[J, N+1]` (the fields of `RkWinAtG`), an exponentially small `μ`
(`|μ| ≤ C_μ (c_s/δ³) e^{-ξ₀/δ³}/δ`, which follows from `|Y| ≤ c_s/δ³`), a monotone decay beyond `q_* + h`, and a support bound `Y_k = 0` for `q_k > R_max`, the mass `Σ_{jz ≤ k < END} Y_k²` beyond the
first lattice site `jz` to the right of `q_* - η` is bounded by `2G²(2κ² + 2κ_m²)(√R₀/π + 2c₂R₀)/(c₁δ²) + K₃'(2κ² + 2κ_m²)/δ`, `R₀ = 2c₂η`.  Here `κ_m > 0` is arbitrary (take it small).  The lattice is `q_k = (k + θ) δ³`, `θ ≥ 0` (`θ = 1/2` integer chains, `θ = 1` half-integer chains).

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma rkza_geom {X : ℤ → ℝ} {J m N jz : ℤ} {δ qs r η c1 c2 θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hη : 0 < η)
    (hηr : η ≤ r / 2) (hη1 : η ≤ 1) (hr : 0 < r) (hs3 : δ ^ 3 ≤ η / 2) (hs4 : δ ^ 2 ≤ c1 * η / (2 * (1 + c2))) (hc2 : 0 < c2)
    (hJN : J < N) (hJm : J ≤ m)
    (hp2 : ((J : ℝ) + θ) * δ ^ 3 < qs - r + δ ^ 3) (hp3 : qs ≤ ((m : ℝ) + θ) * δ ^ 3)
    (hp4 : ((m : ℝ) + θ) * δ ^ 3 < qs + δ ^ 3)
    (hjz1 : qs - η < ((jz : ℝ) + θ) * δ ^ 3) (hjz2 : ((jz : ℝ) + θ) * δ ^ 3 ≤ qs - η + δ ^ 3)
    (gap : ∀ k ∈ Finset.Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hmN : m ≤ N) (X0 : 0 ≤ X m ∧ X m ≤ c2 * δ) :
    J < jz ∧ jz ≤ m ∧ X jz ≤ -1 ∧ -X jz ≤ (2 * c2 * η) / δ ^ 2 ∧ ((m + 2 - jz : ℤ) : ℝ) ≤ 4 / δ ^ 3 := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hJjz : J < jz := by
    by_contra hcon
    push Not at hcon
    have : ((jz : ℝ) + θ) * δ ^ 3 ≤ ((J : ℝ) + θ) * δ ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ hδ3.le
      have : (jz : ℝ) ≤ J := by exact_mod_cast hcon
      linarith
    linarith
  have hjzm : jz ≤ m := by
    by_contra hcon
    push Not at hcon
    have : ((m : ℝ) + θ) * δ ^ 3 < ((jz : ℝ) + θ) * δ ^ 3 := by
      apply mul_lt_mul_of_pos_right _ hδ3
      have : (m : ℝ) < jz := by exact_mod_cast hcon
      linarith
    linarith
  have hmj_lo : η / 2 ≤ ((m - jz : ℤ) : ℝ) * δ ^ 3 := by
    have e : ((m - jz : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + θ) * δ ^ 3 - ((jz : ℝ) + θ) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith
  have hmj_hi : ((m - jz : ℤ) : ℝ) * δ ^ 3 ≤ η + δ ^ 3 := by
    have e : ((m - jz : ℤ) : ℝ) * δ ^ 3 = ((m : ℝ) + θ) * δ ^ 3 - ((jz : ℝ) + θ) * δ ^ 3 := by push_cast; ring
    rw [e]; linarith
  have hgapJ : ∀ k : ℤ, jz ≤ k → k < m → c1 * δ ≤ X (k + 1) - X k := fun k h1 h2 =>
    (gap k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).1
  have hgapU : ∀ k : ℤ, jz ≤ k → k < m → X (k + 1) - X k ≤ c2 * δ := fun k h1 h2 =>
    (gap k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2
  have hsp := kk_span (X := X) (J := jz) (m := m) (ε0 := c1 * δ) hjzm hgapJ
  have hspu := kk_span_up (X := X) (J := jz) (m := m) (ε' := c2 * δ) hjzm hgapU
  refine ⟨hJjz, hjzm, ?_, ?_, ?_⟩
  · have h1 : ((m - jz : ℤ) : ℝ) * (c1 * δ) ≥ c1 * η / (2 * δ ^ 2) := by
      have : ((m - jz : ℤ) : ℝ) ≥ η / (2 * δ ^ 3) := by
        rw [ge_iff_le, div_le_iff₀ (by positivity)]; linarith
      calc ((m - jz : ℤ) : ℝ) * (c1 * δ) ≥ η / (2 * δ ^ 3) * (c1 * δ) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = c1 * η / (2 * δ ^ 2) := by field_simp
    have h2 : 1 + c2 ≤ c1 * η / (2 * δ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + c2))).1 hs4
      nlinarith
    have := X0.2
    have h3 : c2 * δ ≤ c2 := by nlinarith
    linarith
  · have h1 : ((m - jz : ℤ) : ℝ) * (c2 * δ) ≤ (2 * c2 * η) / δ ^ 2 := by
      have : ((m - jz : ℤ) : ℝ) ≤ (η + δ ^ 3) / δ ^ 3 := by rw [le_div_iff₀ hδ3]; linarith
      calc ((m - jz : ℤ) : ℝ) * (c2 * δ) ≤ (η + δ ^ 3) / δ ^ 3 * (c2 * δ) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = c2 * (η + δ ^ 3) / δ ^ 2 := by field_simp
        _ ≤ (2 * c2 * η) / δ ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have : c2 * (η + δ ^ 3) ≤ c2 * (2 * η) := mul_le_mul_of_nonneg_left (by linarith) hc2.le
          linarith
    have := X0.1
    linarith
  · rw [le_div_iff₀ hδ3]
    have e : ((m + 2 - jz : ℤ) : ℝ) * δ ^ 3 = ((m - jz : ℤ) : ℝ) * δ ^ 3 + 2 * δ ^ 3 := by push_cast; ring
    rw [e]
    have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
    linarith

lemma rkza_k1 {X : ℤ → ℝ} {J m N : ℤ} {δ r c1 c2 : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hr : 0 < r)
    (hs5 : δ ≤ c1 * r / 8) (hs6 : c2 * δ ≤ 1) (hJm : J ≤ m) (hJN : J < N) (hmN : m ≤ N)
    (gap : ∀ k ∈ Finset.Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (Xm : ∀ k ∈ Finset.Icc J (m + 1), X k ≤ 1 / 4) (X0 : 0 ≤ X m ∧ X m ≤ c2 * δ) (XN : c1 * (r / 4) / δ ^ 2 ≤ X N) :
    ∃ k1 : ℤ, m + 1 ≤ k1 ∧ k1 < N ∧ X k1 ≤ 1 / δ ∧ 1 / δ < X (k1 + 1) ∧ ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → X k ≤ 2 / δ := by
  have hc2 : 0 < c2 := hc1.trans_le hc12
  have hδ2le : δ ^ 2 ≤ δ := by nlinarith
  have hXmN : m < N := by
    by_contra hcon
    have hNm : N = m := le_antisymm (by omega) hmN
    rw [hNm] at XN
    have h1 : c1 * (r / 4) / δ ^ 2 ≤ c2 * δ := XN.trans X0.2
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : c2 * δ * δ ^ 2 ≤ δ := by
      calc c2 * δ * δ ^ 2 = (c2 * δ) * δ ^ 2 := rfl
        _ ≤ 1 * δ ^ 2 := mul_le_mul_of_nonneg_right hs6 (by positivity)
        _ ≤ δ := by linarith
    have h3 : 0 < c1 * r := by positivity
    linarith
  have hδinv : 1 / 4 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hXNgt : 1 / δ < X N := by
    have h1 : 1 / δ = δ / δ ^ 2 := by field_simp
    have h2 : c1 * (r / 4) / δ ^ 2 = (c1 * r / 4) / δ ^ 2 := by ring
    have h3 : δ / δ ^ 2 < (c1 * r / 4) / δ ^ 2 := by
      apply div_lt_div_of_pos_right _ (by positivity)
      have : 0 < c1 * r := by positivity
      linarith
    linarith
  have hXm1 : X (m + 1) ≤ 1 / 4 := Xm (m + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  obtain ⟨k1, hk11, hk1N, hX1, hX2⟩ := kk_ivt (X := X) (J := m + 1) (b := N) (t := 1 / δ) (by linarith) hXNgt (by omega)
  refine ⟨k1, hk11, hk1N, hX1, hX2, ?_⟩
  have hmonoX : ∀ k ∈ Finset.Icc J N, X k ≤ X (k + 1) := fun k hk => by
    have : 0 ≤ c1 * δ := by positivity
    linarith [(gap k hk).1]
  have hXk1 : X (k1 + 1) ≤ 1 / δ + 1 := by
    have h1 := (gap k1 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2
    have : c2 * δ ≤ 1 := hs6
    linarith
  have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  intro k hk1' hk2'
  have := kc_mono hmonoX k (k1 + 1) hk1' hk2' (by omega)
  have e : 2 / δ = 1 / δ + 1 / δ := by ring
  linarith

lemma rkza_K {Y X g : ℤ → ℝ} {J N k1 : ℤ} {δ C Cmu ξ0 gmax κ μ cs κm : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgmax : 0 ≤ gmax) (hC : 0 ≤ C)
    (hCmu : 0 ≤ Cmu) (hcs : 0 ≤ cs) (hξ0 : 0 < ξ0) (hκm : 0 < κm) (hs1 : δ ≤ ξ0 / 14)
    (hs2 : δ ≤ κm * ξ0 ^ 3 / (48 * ((450 * gmax + C) * Cmu * cs + 1))) (hk1N : k1 < N)
    (gup : ∀ k ∈ Finset.Icc J (N + 1), |g k| ≤ gmax)
    (pt : ∀ k ∈ Finset.Icc J (N + 1), |Y k - (κ * (g k * airyAi (X k)) + μ * (g k * airyBi (X k)))| ≤
      C * δ ^ 3 * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k)))
    (hμ : |μ| ≤ Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ) (hXle : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → X k ≤ 2 / δ) :
    ∃ K : ℝ, 0 ≤ K ∧ K ^ 2 ≤ 2 * κ ^ 2 + 2 * κm ^ 2 ∧ ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 →
      Y k ^ 2 ≤ 2 * gmax ^ 2 * K ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2 := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  set Kmu : ℝ := (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) / δ ^ 3 with hKmu
  have hKmu0 : 0 ≤ Kmu := by positivity
  have hKmuS : Kmu ≤ κm := rk_Kmu_small hδ hδ1 hξ0 hCmu hcs hgmax hC hs1 hs2 hμ
  set K : ℝ := |κ| + Kmu with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hKκ : |κ| ≤ K := by rw [hKdef]; linarith
  have hμE : (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) ≤ δ ^ 3 * K := by
    have e : (450 * gmax + C) * |μ| * Real.exp (7 / δ ^ 2) = δ ^ 3 * Kmu := by
      rw [hKmu]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by rw [hKdef]; linarith [abs_nonneg κ]) hδ3.le
  have hrest : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * K := by
    intro k hk1' hk2'
    have hkmem : k ∈ Finset.Icc J (N + 1) := Finset.mem_Icc.2 ⟨hk1', by omega⟩
    exact rk_rest hC hδ hδ1 hgmax (pt k hkmem) (gup k hkmem) (airyWt_le_one _)
      (kk_biwt_le hδ hδ1 (hXle k hk1' hk2')) (airyBiWt_pos _).le (apx_airyBi_global (X k)).1 hKκ hμE
  refine ⟨K, hK0, ?_, ?_⟩
  · have h1 : K ^ 2 ≤ 2 * |κ| ^ 2 + 2 * Kmu ^ 2 := by nlinarith [sq_nonneg (|κ| - Kmu)]
    have h2 : Kmu ^ 2 ≤ κm ^ 2 := pow_le_pow_left₀ hKmu0 hKmuS 2
    rw [sq_abs] at h1
    linarith
  · intro k hk1' hk2'
    have h := kk_y_le (hrest k hk1' hk2') (gup k (Finset.mem_Icc.2 ⟨hk1', by omega⟩))
    have hκ2 : κ ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs κ]; exact pow_le_pow_left₀ (abs_nonneg _) hKκ 2
    rw [abs_of_nonneg hK0]
    have : 2 * gmax ^ 2 * κ ^ 2 * airyAi (X k) ^ 2 ≤ 2 * gmax ^ 2 * K ^ 2 * airyAi (X k) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hκ2 (by positivity : (0 : ℝ) ≤ 2 * gmax ^ 2)
      nlinarith [sq_nonneg (airyAi (X k)), mul_le_mul_of_nonneg_right this (sq_nonneg (airyAi (X k)))]
    linarith

lemma rk_zone_abs {Y X g : ℤ → ℝ} {J m N jz : ℤ} {δ qs r η C Cmu ξ0 gmin gmax c1 c2 κ μ cs Rmax κm θ : ℝ}
    (hθ : 0 ≤ θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hgmax : 0 ≤ gmax) (hC : 0 ≤ C) (hCmu : 0 ≤ Cmu) (hcs : 0 ≤ cs)
    (hξ0 : 0 < ξ0) (hκm : 0 < κm) (hRmax : 0 ≤ Rmax) (hr : 0 < r) (hη : 0 < η) (hηr : η ≤ r / 2) (hη1 : η ≤ 1)
    (hs1 : δ ≤ ξ0 / 14) (hs2 : δ ≤ κm * ξ0 ^ 3 / (48 * ((450 * gmax + C) * Cmu * cs + 1))) (hs3 : δ ^ 3 ≤ η / 2)
    (hs4 : δ ^ 2 ≤ c1 * η / (2 * (1 + c2))) (hs5 : δ ≤ c1 * r / 8) (hs6 : c2 * δ ≤ 1)
    (hJ1 : 1 ≤ J) (hJN : J < N) (hJm : J ≤ m) (hmN : m ≤ N)
    (hp2 : ((J : ℝ) + θ) * δ ^ 3 < qs - r + δ ^ 3) (hp3 : qs ≤ ((m : ℝ) + θ) * δ ^ 3)
    (hp4 : ((m : ℝ) + θ) * δ ^ 3 < qs + δ ^ 3)
    (hjz1 : qs - η < ((jz : ℝ) + θ) * δ ^ 3) (hjz2 : ((jz : ℝ) + θ) * δ ^ 3 ≤ qs - η + δ ^ 3)
    (gap : ∀ k ∈ Finset.Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (Xm : ∀ k ∈ Finset.Icc J (m + 1), X k ≤ 1 / 4) (X0 : 0 ≤ X m ∧ X m ≤ c2 * δ) (XN : c1 * (r / 4) / δ ^ 2 ≤ X N)
    (gup : ∀ k ∈ Finset.Icc J (N + 1), |g k| ≤ gmax)
    (pt : ∀ k ∈ Finset.Icc J (N + 1), |Y k - (κ * (g k * airyAi (X k)) + μ * (g k * airyBi (X k)))| ≤
      C * δ ^ 3 * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k)))
    (hμ : |μ| ≤ Cmu * (cs / δ ^ 3) * Real.exp (-ξ0 / δ ^ 3) / δ)
    (hmono : ∀ k' k : ℤ, qs + δ ^ 3 ≤ ((k' : ℝ) + θ) * δ ^ 3 → k' ≤ k → Y k ^ 2 ≤ Y k' ^ 2)
    (hsupp : ∀ k : ℤ, Rmax < ((k : ℝ) + θ) * δ ^ 3 → Y k = 0) :
    ∃ END : ℤ, jz ≤ END ∧ (∀ k : ℤ, END ≤ k → Y k = 0) ∧
      ∑ k ∈ Finset.Ico jz END, Y k ^ 2 ≤
        2 * gmax ^ 2 * (2 * κ ^ 2 + 2 * κm ^ 2) * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2)) +
          rkzK3 c1 gmax C 4 (Rmax + 2) * (2 * κ ^ 2 + 2 * κm ^ 2) / δ := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hc2 : 0 < c2 := hc1.trans_le hc12
  obtain ⟨hJjz, hjzm, hXJ, hXJlow, hmcnt⟩ := rkza_geom hδ hδ1 hc1 hη hηr hη1 hr hs3 hs4 hc2 hJN hJm hp2 hp3 hp4 hjz1 hjz2 gap hmN X0
  obtain ⟨k1, hk11, hk1N, hX1, hX2, hXle⟩ := rkza_k1 hδ hδ1 hc1 hc12 hr hs5 hs6 hJm hJN hmN gap Xm X0 XN
  obtain ⟨K, hK0, hK2, hY2⟩ := rkza_K (Y := Y) (X := X) (g := g) (J := J) (N := N) (k1 := k1) hδ hδ1 hgmax hC hCmu hcs hξ0 hκm hs1 hs2
    hk1N gup pt hμ hXle
  have hXm1 : X (m + 1) ≤ 1 / 4 := Xm (m + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  -- the end of the support
  set NN : ℤ := ⌈Rmax / δ ^ 3⌉ + 1 with hNNdef
  have hNN0 : 0 ≤ NN := by
    have : 0 ≤ ⌈Rmax / δ ^ 3⌉ := Int.ceil_nonneg (by positivity)
    omega
  have hNNle : (NN : ℝ) ≤ (Rmax + 2) / δ ^ 3 := by
    have h1 : ((⌈Rmax / δ ^ 3⌉ : ℤ) : ℝ) < Rmax / δ ^ 3 + 1 := Int.ceil_lt_add_one _
    have e : (NN : ℝ) = ((⌈Rmax / δ ^ 3⌉ : ℤ) : ℝ) + 1 := by rw [hNNdef]; push_cast; ring
    have h2 : (Rmax + 2) / δ ^ 3 = Rmax / δ ^ 3 + 2 / δ ^ 3 := by ring
    have h3 : 2 ≤ 2 / δ ^ 3 := by
      rw [le_div_iff₀ hδ3]
      have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
      linarith
    rw [e, h2]; linarith
  have hmono' : ∀ k : ℤ, k1 + 1 ≤ k → Y k ^ 2 ≤ Y (k1 + 1) ^ 2 := by
    intro k hk
    refine hmono (k1 + 1) k ?_ hk
    have : (m : ℝ) + 1 ≤ (k1 : ℝ) := by exact_mod_cast hk11
    have : ((m : ℝ) + θ) * δ ^ 3 + δ ^ 3 ≤ (((k1 + 1 : ℤ) : ℝ) + θ) * δ ^ 3 := by
      push_cast; nlinarith
    linarith
  have Z := rkz_zone (X := X) (Y := Y) (jz := jz) (m := m) (k1 := k1) (NN := NN) (δ := δ) (G := gmax) (C := C) (c1 := c1)
    (c2 := c2) (K := K) (R0 := 2 * c2 * η) (Rc := 4) (Rt := Rmax + 2) hδ hδ1 hc1 hc2.le hC (by positivity) (by norm_num)
    (by positivity) hjzm hk11 hNN0
    (fun k h1 h2 => gap k (Finset.mem_Icc.2 ⟨by omega, by omega⟩)) X0.1 hXm1 hX1 hX2 hXJ hXJlow hmcnt
    (fun k h1 h2 => hY2 k (by omega) h2) hNNle hmono'
  refine ⟨k1 + 1 + NN, by omega, ?_, ?_⟩
  · intro k hk
    apply hsupp
    have h1 : Rmax / δ ^ 3 < (NN : ℝ) := by
      have := Int.le_ceil (Rmax / δ ^ 3)
      have e : (NN : ℝ) = ((⌈Rmax / δ ^ 3⌉ : ℤ) : ℝ) + 1 := by rw [hNNdef]; push_cast; ring
      linarith
    have h2 : Rmax < (NN : ℝ) * δ ^ 3 := by
      rwa [div_lt_iff₀ hδ3] at h1
    have h3 : (NN : ℝ) + 0 ≤ (k : ℝ) := by
      have : ((k1 + 1 + NN : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk1' : (0 : ℝ) ≤ (k1 : ℝ) := by
        have : (0 : ℤ) ≤ k1 := by omega
        exact_mod_cast this
      push_cast at this
      linarith
    have : (NN : ℝ) * δ ^ 3 ≤ ((k : ℝ) + θ) * δ ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hδ3.le
    linarith
  · refine Z.trans ?_
    unfold rkzK3
    have hb1 : 0 ≤ 2 * gmax ^ 2 * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2)) := by positivity
    have hb2 : 0 ≤ (2 * gmax ^ 2 * (49 / (4 * c1) + 18) + 2 * (C + 1) ^ 2 * 4 +
        (18 * gmax ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) +
          (Rmax + 2) * (54 * gmax ^ 2 + 2 * (C + 1) ^ 2)) / δ := by positivity
    have e1 : 2 * gmax ^ 2 * K ^ 2 * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2)) =
        K ^ 2 * (2 * gmax ^ 2 * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2))) := by ring
    have e2 : 2 * gmax ^ 2 * (2 * κ ^ 2 + 2 * κm ^ 2) * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2)) =
        (2 * κ ^ 2 + 2 * κm ^ 2) * (2 * gmax ^ 2 * ((√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / (c1 * δ ^ 2))) := by ring
    have e3 : ∀ B : ℝ, B * K ^ 2 / δ = K ^ 2 * (B / δ) := fun B => by ring
    have e4 : ∀ B : ℝ, B * (2 * κ ^ 2 + 2 * κm ^ 2) / δ = (2 * κ ^ 2 + 2 * κm ^ 2) * (B / δ) := fun B => by ring
    rw [e1, e3, e2, e4]
    have := mul_le_mul_of_nonneg_right hK2 hb1
    have h' := mul_le_mul_of_nonneg_right hK2 hb2
    linarith

/-- info: 'FormalResearch.Special.rk_zone_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_zone_abs

end FormalResearch.Special
